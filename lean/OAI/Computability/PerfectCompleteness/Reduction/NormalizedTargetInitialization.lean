import OAI.Computability.PerfectCompleteness.Machines.ExactTargetOdometer
import OAI.Computability.PerfectCompleteness.Machines.SourceClauseCountMachine
import OAI.Computability.PerfectCompleteness.Machines.TupleInitializationMachine

namespace OAI


namespace PerfectCompleteness.NormalizedTargetInitialization


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) := SignedTupleLayout.Tape width (Fin 4)
abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (A : Type) := A × Option Bool

def clean {A : Type} (ambient : A) : State A := (ambient, none)

variable {width : Nat}

def countTape : Fin 4 → Tape width
  | 0 => .source .table
  | 1 => .extra 1
  | 2 => .extra 2
  | 3 => .extra 0

theorem countTape_injective : Function.Injective (countTape (width := width)) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [countTape] at same ⊢

def currents (width : Nat) : List (Tape width) := List.ofFn SignedTupleLayout.Tape.current
def remaining (width : Nat) : List (Tape width) := List.ofFn SignedTupleLayout.Tape.remaining

theorem destinations_nodup (width : Nat) : (currents width ++ remaining width).Nodup := by
  unfold currents remaining
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j same
    simpa using same
  · apply List.nodup_ofFn.mpr
    intro i j same
    simpa using same
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    intro same
    cases same

theorem count_not_destination :
    (SignedTupleLayout.Tape.extra 0 : Tape width) ∉ currents width ++ remaining width := by
  simp [currents, remaining, List.mem_ofFn]

inductive Label
  | seed
  | count (label : SourceClauseCountMachine.Label)
  | tuple (label : TupleInitializationMachine.Label)
  deriving DecidableEq, Fintype

variable {Λ A : Type}

def instruction (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (width := width)) Λ (State A)
  | .seed => .push (.extra 0) (fun _ => false)
      (.push .edgeCount (fun _ => false)
        (.load (fun state => clean state.1)
          (.goto (fun _ => labels (.count SourceClauseCountMachine.main)))))
  | .count label => SourceClauseCountMachine.instruction countTape
      (fun l => labels (.count l)) (some (labels (.tuple .seed))) rejected label
  | .tuple label => TupleInitializationMachine.instruction (.extra 0)
      (currents width) (remaining width) (fun l => labels (.tuple l)) done label

theorem instruction_pushBound (labels : Label → Λ) (done rejected : Option Λ) (label : Label) :
    Runtime.statementPushBound (instruction (width := width) (A := A) labels done rejected label) ≤
      2 * width + 2 := by
  have exitBound (destination : Tape width) (exit : Option Λ) :
      Runtime.statementPushBound
        (UniqueGamesTheorem.Reduction.MachineTransfer.exitAt
          (Γ := Alphabet (width := width)) (σ := A) destination exit) = 0 := by
    cases exit <;> rfl
  cases label with
  | seed => simp [instruction, Runtime.statementPushBound]
  | count label =>
      cases label <;>
        simp [instruction, SourceClauseCountMachine.instruction,
          UniqueGamesTheorem.Reduction.MachineTransfer.loopAt, MachineCopy.forkLoop,
          UnaryBlockSkipMachine.instruction, UnaryBlockSkipMachine.finish,
          UniqueGamesTheorem.Foundations.Hastad.SourceMachine.fieldLoop,
          MachineDrain.drain, Runtime.statementPushBound, exitBound]
  | tuple label =>
      have bound := TupleInitializationMachine.instruction_pushBound
        (σ := A) (SignedTupleLayout.Tape.extra 0 : Tape width)
        (currents width) (remaining width) (fun l => labels (.tuple l)) done label
      change Runtime.statementPushBound
        (TupleInitializationMachine.instruction (.extra 0)
          (currents width) (remaining width) (fun l => labels (.tuple l)) done label) ≤ _
      refine bound.trans ?_
      simp only [currents, remaining, List.length_ofFn]
      omega

def inputTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool
  | .source .table => NormalizedSourceInput.bits input
  | _ => []

def seededTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (Function.update (inputTapes input) (.extra 0) [false]) .edgeCount [false]

def countedTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (seededTapes input) (.extra 0)
    (encodeWord (NormalizedSourceInput.clauseCount input))

def zeroDigits (input : NormalizedSourceInput.Input) :
    Fin width → Fin (NormalizedSourceInput.clauseCount input) :=
  fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩

def readyTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (ExactTargetOdometer.baseTapes input (zeroDigits input) (fun _ => []))
    .edgeCount (encodeWord 0)

@[simp] theorem seeded_count (input : NormalizedSourceInput.Input) :
    seededTapes (width := width) input (.extra 0) = [false] := by
  simp [seededTapes]

@[simp] theorem counted_count (input : NormalizedSourceInput.Input) :
    countedTapes (width := width) input (.extra 0) =
      encodeWord (NormalizedSourceInput.clauseCount input) := by
  simp [countedTapes]

theorem initializedTapes_eq_ready (input : NormalizedSourceInput.Input) :
    TupleInitializationMachine.initializedTapes (.extra 0) (currents width) (remaining width)
        (countedTapes input) (NormalizedSourceInput.clauseCount input - 1) [] =
      readyTapes input := by
  funext key
  cases key with
  | source source =>
      cases source <;>
        simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
          currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
          readyTapes, ExactTargetOdometer.baseTapes]
  | current position =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes, zeroDigits, encodeWord]
  | remaining position =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes, zeroDigits, encodeWord]
  | encodedVariable position slot =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | adapterScratch =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | edgeWork slot =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | edgeCount =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes,
        readyTapes, encodeWord]
  | extra slot =>
      fin_cases slot <;>
        simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
          currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
          readyTapes, ExactTargetOdometer.baseTapes]

@[simp] theorem ready_table (input : NormalizedSourceInput.Input) :
    readyTapes (width := width) input (.source .table) = NormalizedSourceInput.bits input := by
  simp [readyTapes, ExactTargetOdometer.baseTapes]

@[simp] theorem ready_current (input : NormalizedSourceInput.Input) (position : Fin width) :
    readyTapes input (.current position) = encodeWord 0 := by
  simp [readyTapes, ExactTargetOdometer.baseTapes, zeroDigits]

@[simp] theorem ready_remaining (input : NormalizedSourceInput.Input) (position : Fin width) :
    readyTapes input (.remaining position) =
      encodeWord (NormalizedSourceInput.clauseCount input - 1) := by
  simp [readyTapes, ExactTargetOdometer.baseTapes, zeroDigits]

@[simp] theorem ready_extra (input : NormalizedSourceInput.Input) (slot : Fin 4) :
    readyTapes (width := width) input (.extra slot) = [] := by
  simp [readyTapes, ExactTargetOdometer.baseTapes]

theorem ready_eq_native {branch : Nat → Nat} {n t : Nat}
    (input : NormalizedSourceInput.Input) :
    readyTapes (width := TreeCanonical.locationCount branch n t) input =
      ExactTargetOdometer.nativeTapes (branch := branch) (n := n) (t := t)
        input (zeroDigits input) ⟨[], [], [], 0⟩ (fun _ : Fin 4 => []) := by
  funext key
  cases key with
  | source source =>
      cases source <;>
        simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
          ExactTargetOdometer.baseTapes]
  | current position =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | remaining position =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | encodedVariable position slot =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | adapterScratch =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | edgeWork slot =>
      fin_cases slot <;>
        simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
          ExactTargetOdometer.baseTapes, CanonicalVertexNames.tokens]
  | edgeCount =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | extra slot =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]

variable (labels : Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction labels done rejected label)

include atLabels in
theorem seedStep (input : NormalizedSourceInput.Input) (ambient : A) (register : Option Bool) :
    TM2.step program ⟨some (labels .seed), (ambient, register), inputTapes input⟩ =
      some ⟨some (labels (.count SourceClauseCountMachine.main)), clean ambient, seededTapes input⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [atLabels .seed]
  simp [instruction, TM2.stepAux, seededTapes, inputTapes, clean]

def initializeExactInTime (input : NormalizedSourceInput.Input)
    (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (1 + 3 * ((NormalizedSourceInput.bits input).length + 1) +
        (NormalizedSourceInput.clauseCount input + 1)) := by
  have seeded : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨some (labels (.count SourceClauseCountMachine.main)),
        clean ambient, seededTapes input⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    exact seedStep labels done rejected program atLabels input ambient register
  have counted : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.count SourceClauseCountMachine.main)), clean ambient, seededTapes input⟩
      (some ⟨some (labels (.tuple .seed)), clean ambient, countedTapes input⟩)
      (3 * ((NormalizedSourceInput.bits input).length + 1)) := by
    have run := SourceClauseCountMachine.countInTime countTape countTape_injective
      (fun label => labels (.count label)) (some (labels (.tuple .seed))) rejected
      program (fun label => atLabels (.count label)) (seededTapes input) ambient input.formula
      (by simp [countTape, seededTapes, inputTapes, NormalizedSourceInput.bits])
      (by simp [countTape, seededTapes, inputTapes])
      (by simp [countTape, seededTapes, inputTapes])
    simpa only [SourceClauseCountMachine.clean, clean, countTape, countedTapes, seeded_count,
      NormalizedSourceInput.bits, NormalizedSourceInput.clauseCount, encodeWord] using run
  have initialized : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.tuple .seed)), clean ambient, countedTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (NormalizedSourceInput.clauseCount input + 1) := by
    have run := TupleInitializationMachine.initializeInTime (σ := A)
      (SignedTupleLayout.Tape.extra 0 : Tape width)
      (currents width) (remaining width) (destinations_nodup width) count_not_destination
      (fun label => labels (.tuple label)) done program
      (fun label => by simpa only [instruction] using atLabels (.tuple label))
      (countedTapes input) ambient (NormalizedSourceInput.clauseCount input)
      (NormalizedSourceInput.clauseCount_positive input) []
      (by simp only [counted_count, List.append_nil])
    simpa only [TupleInitializationMachine.clean, clean, initializedTapes_eq_ready] using run
  have first := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seeded counted
  have full := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first initialized
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem count_length_le (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.clauseCount input + 1 ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

def initializeInTime (input : NormalizedSourceInput.Input) (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (4 * ((NormalizedSourceInput.bits input).length + 1)) := by
  let run := initializeExactInTime labels done rejected program atLabels input ambient register
  refine
    { steps := run.steps
      evals_in_steps := run.evals_in_steps
      steps_le_m := run.steps_le_m.trans ?_ }
  have bounded := count_length_le input
  omega

theorem finite_tapes : Finite (Tape width) := inferInstance
theorem finite_state [Finite A] : Finite (State A) := inferInstance
theorem finite_alphabet (key : Tape width) : Finite (Alphabet key) := inferInstance

end
end PerfectCompleteness.NormalizedTargetInitialization

end OAI
