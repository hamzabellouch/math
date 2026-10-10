import OAI.Computability.PerfectCompleteness.Foundations.SignedScheduleIndex
import OAI.Computability.PerfectCompleteness.Machines.CompletedEdgeMachine

namespace OAI


namespace PerfectCompleteness.SignedDescriptorStageMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

local notation "width" => TreeCanonical.locationCount branch n t

abbrev Descriptor := SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large

abbrev Context (A : Type) := A × Option (Descriptor (rows := rows) (repeats := repeats) hq large)

abbrev State (A : Type) :=
  CompletedEdgeMachine.State (Context (rows := rows) (repeats := repeats) hq large A)

def clean {A : Type} (ambient : A) : State (rows := rows) (repeats := repeats) hq large A :=
  CompletedEdgeMachine.clean (ambient, none)

def loaded {A : Type} (ambient : A)
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    State (rows := rows) (repeats := repeats) hq large A :=
  CompletedEdgeMachine.clean (ambient, some descriptor)

def save {A : Type} (state : State (rows := rows) (repeats := repeats) hq large A)
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    State (rows := rows) (repeats := repeats) hq large A := loaded hq large state.1.1.1 descriptor

inductive Label (α : Type) (locations : Nat)
  | load
  | dispatch
  | edge (descriptor : α) (localLabel : CompletedEdgeMachine.Label locations)
  | finish
  deriving DecidableEq, Fintype

theorem state_finite {A : Type} [Finite A] :
    Finite (State (rows := rows) (repeats := repeats) hq large A) := inferInstance

theorem label_finite :
    Finite (Label (Descriptor (rows := rows) (repeats := repeats) hq large) width) := inferInstance

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "StageLabel" => Label (Descriptor (rows := rows) (repeats := repeats) hq large) width

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def selected (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (state : State (rows := rows) (repeats := repeats) hq large A) :
    Descriptor (rows := rows) (repeats := repeats) hq large :=
  state.1.1.2.getD
    (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns state.1.1.1) i)

def finish (count : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A) :=
  .push count (fun _ => true)
    (.load (fun state => clean hq large state.1.1.1)
      (match exit with | none => .halt | some label => .goto (fun _ => label)))

theorem finish_trace (count : K) (exit : Option Λ)
    (state : State (rows := rows) (repeats := repeats) hq large A)
    (base : K → List Bool) :
    TM2.stepAux (finish hq large count exit) state base =
      ⟨exit, clean hq large state.1.1.1, Function.update base count (true :: base count)⟩ := by
  cases exit <;> rfl

omit [DecidableEq K] in
theorem finish_pushBound (count : K) (exit : Option Λ) :
    Runtime.statementPushBound
      (finish (rows := rows) (repeats := repeats) (A := A) hq large count exit) = 1 := by
  cases exit <;> rfl

variable [Fintype A] [DecidableEq A]

def instruction (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (count : K)
    (labels : StageLabel → Λ) (exit rejected : Option Λ) :
    StageLabel → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A)
  | .load => SignedScheduleIndex.instruction hq large hn hbranch hrows
      (fun state : State (rows := rows) (repeats := repeats) hq large A => selectSigns state.1.1.1)
      (save hq large) i (labels .dispatch)
  | .dispatch => .goto (fun state =>
      labels (.edge (selected hq large hn hbranch hrows selectSigns i state)
        (CompletedEdgeMachine.main width)))
  | .edge descriptor localLabel => CompletedEdgeMachine.instruction hq large descriptor
      source work (fun l => labels (.edge descriptor l)) (labels .finish) rejected localLabel
  | .finish => finish hq large count exit

def finalTapes (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (work : Fin 10 → K) (count : K)
    (base : K → List Bool) (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : K → List Bool :=
  let edgeTapes : K → List Bool := CompletedEdgeMachine.finalTapes hq large descriptor work base
    leftPrefix rightPrefix ids vars
  Function.update edgeTapes count (true :: edgeTapes count)

theorem finalTapes_frame (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (work : Fin 10 → K) (count : K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) (k : K)
    (notLeft : k ≠ work 1) (notRight : k ≠ work 8)
    (notOutput : k ≠ work 7) (notCount : k ≠ count) :
    finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars k = base k := by
  simp only [finalTapes, Function.update_of_ne notCount]
  exact CompletedEdgeMachine.finalTapes_frame hq large descriptor work base
    leftPrefix rightPrefix ids vars k notLeft notRight notOutput

theorem finalTapes_count (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (work : Fin 10 → K) (count : K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (notLeft : count ≠ work 1) (notRight : count ≠ work 8) (notOutput : count ≠ work 7) :
    finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars count =
      true :: base count := by
  simp only [finalTapes, Function.update_self]
  rw [CompletedEdgeMachine.finalTapes_frame hq large descriptor work base
    leftPrefix rightPrefix ids vars count notLeft notRight notOutput]

private theorem stageBudget (cost : Nat) : 1 + (cost + (1 + 1)) ≤ cost + 3 := by
  omega

private def stageInTimeForDescriptor (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (descriptor : Descriptor (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ j, Function.Injective (source j))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ j, source j 4 = work 5) (sharedOutput : ∀ j, source j 5 = work 9)
    (sourceAvoid : ∀ j field k, KeyMetadataMachine.idTape (source j) field ≠ work k)
    (count : K) (labels : StageLabel → Λ) (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A))
    (atLabels : ∀ label, program (labels label) =
      instruction (branch := branch) (n := n) (t := t) (q := q)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows
        selectSigns i source work count labels exit rejected label)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ j field, base (KeyMetadataMachine.idTape (source j) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids j) (vars j) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = [])
    (selectedEq : SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i = descriptor) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large descriptor source base leftPrefix rightPrefix ids vars + 3) := by
  let edgeTapes : K → List Bool := CompletedEdgeMachine.finalTapes
    (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
    hq large descriptor work base
    leftPrefix rightPrefix ids vars
  have loadRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨some (labels .dispatch), loaded hq large ambient descriptor, base⟩) 1 := by
    have run := SignedScheduleIndex.inTime (branch := branch) (n := n) (t := t) (q := q)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
      (fun state : State (rows := rows) (repeats := repeats) hq large A => selectSigns state.1.1.1)
      (save hq large) i (labels .dispatch) program (labels .load)
      (atLabels .load) (clean hq large ambient) base
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨some (labels .dispatch), loaded hq large ambient
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i),
        base⟩) 1 at run
    rw [selectedEq] at run
    exact run
  have dispatchRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .dispatch), loaded hq large ambient descriptor, base⟩
      (some ⟨some (labels (.edge descriptor (CompletedEdgeMachine.main width))),
        loaded hq large ambient descriptor, base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .dispatch))
      (loaded hq large ambient descriptor) base) = _
    rw [atLabels .dispatch]
    rfl
  have edgeRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.edge descriptor (CompletedEdgeMachine.main width))),
        loaded hq large ambient descriptor, base⟩
      (some ⟨some (labels .finish), loaded hq large ambient descriptor, edgeTapes⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large descriptor
        source base leftPrefix rightPrefix ids vars) :=
    CompletedEdgeMachine.edgeInTime (branch := branch) (n := n) (t := t) (q := q)
      (rows := rows) (repeats := repeats) hq large descriptor ids vars source sourceDistinct
      work workDistinct sharedScratch sharedOutput sourceAvoid
      (fun l => labels (.edge descriptor l)) (labels .finish) rejected program
      (fun l => atLabels (.edge descriptor l)) base (ambient, some descriptor)
      leftPrefix rightPrefix sourceWords leftDictionary rightDictionary empty
  have finishRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .finish), loaded hq large ambient descriptor, edgeTapes⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .finish))
      (loaded hq large ambient descriptor) edgeTapes) = _
    rw [atLabels .finish]
    change some (TM2.stepAux (finish hq large count exit)
      (loaded hq large ambient descriptor) edgeTapes) = _
    rw [finish_trace]
    rfl
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ loadRun dispatchRun)
      edgeRun) finishRun
  exact
    { steps := joined.steps
      evals_in_steps := joined.evals_in_steps
      steps_le_m := joined.steps_le_m.trans (stageBudget _) }

def stageInTime (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ j, Function.Injective (source j))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ j, source j 4 = work 5) (sharedOutput : ∀ j, source j 5 = work 9)
    (sourceAvoid : ∀ j field k, KeyMetadataMachine.idTape (source j) field ≠ work k)
    (count : K) (labels : StageLabel → Λ) (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A))
    (atLabels : ∀ label, program (labels label) =
      instruction (branch := branch) (n := n) (t := t) (q := q)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows
        selectSigns i source work count labels exit rejected label)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ j field, base (KeyMetadataMachine.idTape (source j) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids j) (vars j) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large
          (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
            (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
          work count base leftPrefix rightPrefix ids vars⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
        source base leftPrefix rightPrefix ids vars + 3) :=
  stageInTimeForDescriptor (branch := branch) (n := n) (t := t) (q := q)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
    (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
    ids vars source sourceDistinct work workDistinct sharedScratch sharedOutput sourceAvoid
    count labels exit rejected program atLabels base ambient leftPrefix rightPrefix
    sourceWords leftDictionary rightDictionary empty rfl

end
end PerfectCompleteness.SignedDescriptorStageMachine

end OAI
