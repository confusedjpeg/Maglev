--------------------------- MODULE TransferRules ---------------------------
(* Models how governance rules hold and release a transfer across Kotlin and Rust:
     - EngineHost.kt (evaluateGovernance, startup hold, active blocks)
     - scheduler.rs (EXEMPTABLE_TAGS, tag_blocks, plan)
     - engine.rs (pause, resume, resume_anyway, tick plan + apply with user_gen guard)

   Rules are plain strings pushed by Kotlin into Rust's `blocked` set. Some rules
   can be overridden per transfer ("Resume anyway"), safety and physical rules
   never can, `seed_metered` applies only while seeding, `storage_full` applies
   only while downloading, and a user pause always wins over rule changes — even
   when it lands between a tick's plan() snapshot and apply_action() (issue #276). *)

CONSTANTS
  DESIGN  \* "shipped", "overrideBypassesAll", "overrideLeaksToSeeding", "userPauseOverwritten", or "noGenGuard"

Exemptable    == {"wifi_only", "battery", "schedule", "seed_metered"}
NonExemptable == {"vpn_required", "storage_full", "startup"}
AllBlocks     == Exemptable \cup NonExemptable

VARIABLES
  phase,                \* "downloading" or "seeding"
  running,              \* TRUE while librqbit is actively transferring
  userPaused,           \* ground truth: the user paused this transfer and has not resumed it
  pausedBy,             \* persisted meta.paused_by: "none", "user", or a tag in AllBlocks
  allowedAnyway,        \* persisted meta.allowed_anyway ("Resume anyway")
  allowedAnywaySeeding, \* persisted meta.allowed_anyway_seeding (override granted while already seeding)
  blocks,               \* active governance tags in Rust's Engine.blocked
  plannedAction,        \* pending tick action: "none", "resume", or a tag in AllBlocks (Pause)
  planStale             \* TRUE if user_gen was bumped after TickPlan took its snapshot

vars == <<phase, running, userPaused, pausedBy, allowedAnyway, allowedAnywaySeeding,
          blocks, plannedAction, planStale>>

TypeOK ==
  /\ phase \in {"downloading", "seeding"}
  /\ running \in BOOLEAN
  /\ userPaused \in BOOLEAN
  /\ pausedBy \in ({"none", "user"} \cup AllBlocks)
  /\ allowedAnyway \in BOOLEAN
  /\ allowedAnywaySeeding \in BOOLEAN
  /\ blocks \subseteq AllBlocks
  /\ plannedAction \in ({"none", "resume"} \cup AllBlocks)
  /\ planStale \in BOOLEAN

\* Exact Rust tag_blocks(tag, facts) logic from scheduler.rs.
TagBlocks(tag, ph, exempt) ==
  IF tag = "seed_metered" /\ ph /= "seeding" THEN FALSE
  ELSE IF tag = "storage_full" /\ ph /= "downloading" THEN FALSE
  ELSE IF DESIGN = "overrideBypassesAll" THEN ~exempt
  ELSE ~(exempt /\ tag \in Exemptable)

\* Pick one blocking tag from bset that applies to (ph, exempt), or "none".
BlockingTag(bset, ph, exempt) ==
  LET matching == {t \in bset : TagBlocks(t, ph, exempt)}
  IN IF matching = {} THEN "none" ELSE CHOOSE t \in matching : TRUE

\* Reconcile (running', pausedBy') via scheduler.rs plan().
Reconcile(curPausedBy, bset, ph, exempt) ==
  IF curPausedBy = "user" /\ DESIGN /= "userPauseOverwritten" THEN
    [run |-> FALSE, by |-> "user"]
  ELSE
    LET blocker == BlockingTag(bset, ph, exempt)
    IN IF blocker /= "none" THEN
         [run |-> FALSE, by |-> blocker]
       ELSE IF curPausedBy = "user" THEN
         [run |-> FALSE, by |-> "user"]
       ELSE
         [run |-> TRUE, by |-> "none"]

\* What Action::Pause / Action::Resume plan() emits for the current state (or "none" if no change).
PlannedOf(curRun, curPausedBy, bset, ph, exempt) ==
  LET res == Reconcile(curPausedBy, bset, ph, exempt)
  IN IF res.run = curRun /\ res.by = curPausedBy THEN "none"
     ELSE IF res.run THEN "resume"
     ELSE res.by

Init ==
  /\ phase = "downloading"
  /\ running = TRUE
  /\ userPaused = FALSE
  /\ pausedBy = "none"
  /\ allowedAnyway = FALSE
  /\ allowedAnywaySeeding = FALSE
  /\ blocks = {}
  /\ plannedAction = "none"
  /\ planStale = FALSE

\* Step 1 of Engine::tick(): snapshot facts + user_gen and compute plan().
TickPlan ==
  /\ plannedAction = "none"
  /\ LET act == PlannedOf(running, pausedBy, blocks, phase, allowedAnyway)
     IN /\ act /= "none"
        /\ plannedAction' = act
        /\ planStale' = FALSE
  /\ UNCHANGED <<phase, running, userPaused, pausedBy, allowedAnyway, allowedAnywaySeeding, blocks>>

\* Step 2 of Engine::tick(): apply_action checks user_gen == snap_gen (skipped in "noGenGuard").
TickApply ==
  /\ plannedAction /= "none"
  /\ IF DESIGN /= "noGenGuard" /\ planStale THEN
       /\ plannedAction' = "none"
       /\ planStale' = FALSE
       /\ UNCHANGED <<phase, running, userPaused, pausedBy, allowedAnyway, allowedAnywaySeeding, blocks>>
     ELSE IF plannedAction = "resume" THEN
       /\ running' = TRUE
       /\ pausedBy' = "none"
       /\ plannedAction' = "none"
       /\ planStale' = FALSE
       /\ UNCHANGED <<phase, userPaused, allowedAnyway, allowedAnywaySeeding, blocks>>
     ELSE
       /\ running' = FALSE
       /\ pausedBy' = plannedAction
       /\ plannedAction' = "none"
       /\ planStale' = FALSE
       /\ UNCHANGED <<phase, userPaused, allowedAnyway, allowedAnywaySeeding, blocks>>

\* Kotlin pushes a rule block (e.g. mobile data, VPN dropped, low battery, schedule, low storage).
RuleTurnsOn(t) ==
  /\ plannedAction = "none"
  /\ t \in (AllBlocks \ {"startup"})
  /\ t \notin blocks
  /\ LET nextBlocks == blocks \cup {t}
         act == PlannedOf(running, pausedBy, nextBlocks, phase, allowedAnyway)
     IN /\ blocks' = nextBlocks
        /\ plannedAction' = act
        /\ planStale' = FALSE
  /\ UNCHANGED <<phase, running, userPaused, pausedBy, allowedAnyway, allowedAnywaySeeding>>

\* Kotlin lifts a rule block when the condition clears.
RuleTurnsOff(t) ==
  /\ plannedAction = "none"
  /\ t \in blocks
  /\ LET nextBlocks == blocks \ {t}
         act == PlannedOf(running, pausedBy, nextBlocks, phase, allowedAnyway)
     IN /\ blocks' = nextBlocks
        /\ plannedAction' = act
        /\ planStale' = FALSE
  /\ UNCHANGED <<phase, running, userPaused, pausedBy, allowedAnyway, allowedAnywaySeeding>>

\* The user pauses the transfer: can land even while a tick's plannedAction is waiting to apply!
\* Bumps user_gen, marking any in-flight plannedAction stale.
YouPause ==
  /\ ~userPaused
  /\ userPaused' = TRUE
  /\ pausedBy' = "user"
  /\ running' = FALSE
  /\ allowedAnyway' = FALSE
  /\ allowedAnywaySeeding' = FALSE
  /\ planStale' = IF plannedAction /= "none" THEN TRUE ELSE planStale
  /\ UNCHANGED <<phase, blocks, plannedAction>>

\* The user taps Resume (without override): clears user pause, bumps user_gen.
YouResume ==
  /\ userPaused
  /\ userPaused' = FALSE
  /\ pausedBy' = "none"
  /\ planStale' = IF plannedAction /= "none" THEN TRUE ELSE planStale
  /\ UNCHANGED <<phase, running, allowedAnyway, allowedAnywaySeeding, blocks, plannedAction>>

\* The user taps "Resume anyway": sets allowed_anyway (and remembers if already seeding), bumps user_gen.
YouResumeAnyway ==
  /\ ~running
  /\ plannedAction = "none"
  /\ LET nextSeeding == (phase = "seeding")
         act == PlannedOf(running, "none", blocks, phase, TRUE)
     IN /\ userPaused' = FALSE
        /\ pausedBy' = "none"
        /\ allowedAnyway' = TRUE
        /\ allowedAnywaySeeding' = nextSeeding
        /\ plannedAction' = act
        /\ planStale' = FALSE
  /\ UNCHANGED <<phase, running, blocks>>

\* A downloading transfer finishes: engine.rs drops allowed_anyway unless granted while already seeding.
DownloadFinishes ==
  /\ plannedAction = "none"
  /\ phase = "downloading"
  /\ running
  /\ LET nextExempt == IF DESIGN = "overrideLeaksToSeeding" THEN allowedAnyway
                       ELSE IF allowedAnyway /\ ~allowedAnywaySeeding THEN FALSE
                       ELSE allowedAnyway
         res == Reconcile(pausedBy, blocks, "seeding", nextExempt)
     IN /\ phase' = "seeding"
        /\ allowedAnyway' = nextExempt
        /\ running' = res.run
        /\ pausedBy' = res.by
  /\ UNCHANGED <<userPaused, allowedAnywaySeeding, blocks, plannedAction, planStale>>

\* Engine restarts: nativeInit holds every transfer with "startup" until Kotlin evaluates governance.
EngineRestarts ==
  /\ plannedAction = "none"
  /\ "startup" \notin blocks
  /\ LET nextBlocks == blocks \cup {"startup"}
         res == Reconcile(pausedBy, nextBlocks, phase, allowedAnyway)
     IN /\ blocks' = nextBlocks
        /\ running' = res.run
        /\ pausedBy' = res.by
  /\ UNCHANGED <<phase, userPaused, allowedAnyway, allowedAnywaySeeding, plannedAction, planStale>>

Next ==
  \/ TickPlan
  \/ TickApply
  \/ \E t \in (AllBlocks \ {"startup"}) : RuleTurnsOn(t)
  \/ \E t \in AllBlocks : RuleTurnsOff(t)
  \/ YouPause
  \/ YouResume
  \/ YouResumeAnyway
  \/ DownloadFinishes
  \/ EngineRestarts

Spec == Init /\ [][Next]_vars

\* --- Rules (invariants) ---

\* A transfer the user paused never runs and never keeps an old "Resume anyway" override.
UserPauseStaysPaused ==
  userPaused => (~running /\ ~allowedAnyway)

\* Safety and physical rules (VPN, low storage while downloading, startup hold) always stop
\* the transfer once the pending tick has applied, even if the user tapped "Resume anyway".
SafetyRulesAlwaysHold ==
  (plannedAction = "none" /\ (
    "vpn_required" \in blocks
    \/ ("storage_full" \in blocks /\ phase = "downloading")
    \/ "startup" \in blocks )) => ~running

\* A "Resume anyway" tapped during a download never leaks into seeding on a metered link.
NoSeedLeak ==
  (plannedAction = "none" /\ phase = "seeding" /\ ~allowedAnywaySeeding
    /\ ("seed_metered" \in blocks \/ "wifi_only" \in blocks))
    => ~running

\* When no tick is mid-flight, the user didn't pause it, and no active rule applies,
\* the transfer is never stuck with a stale rule tag once the tick runs.
NoStuckRuleTag ==
  (plannedAction = "none" /\ ~userPaused /\ BlockingTag(blocks, phase, allowedAnyway) = "none"
    /\ PlannedOf(running, pausedBy, blocks, phase, allowedAnyway) = "none")
    => (running /\ pausedBy = "none")
=============================================================================
