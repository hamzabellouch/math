import OAI.Computability.PerfectCompleteness.Foundations.SourceTuplePlacement
import OAI.Computability.PerfectCompleteness.Machines.SourceTupleResetMachine
import OAI.Computability.UniqueGames.Machines.MachineRegularLift

namespace OAI


namespace PerfectCompleteness.SourceTupleResetPlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding

abbrev Tape (width : Nat) := SourceTupleData.Tape width
abbrev Label (width : Nat) := SourceTupleResetMachine.Label width
abbrev State (A : Type) := SourceTupleResetMachine.State A
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {width : Nat} {K Λ A : Type}

def nativeProgram : Label width →
    TM2.Stmt (Alphabet (K := Tape width)) (Label width) (State A) :=
  SourceTupleResetMachine.instruction id none

def instruction (tape : Tape width → K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  fun label => Placement.statement tape labels exit (nativeProgram label)

def entry (labels : Label width → Λ) (exit : Option Λ) : Option Λ :=
  Placement.label labels exit (SourceTupleResetMachine.entry id none)

variable [DecidableEq K]

theorem resetTrace (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (ambient : A) :
    (advance (TM2.step program))^[SourceTupleResetMachine.steps formula indices]
      (some ⟨entry labels exit, (ambient, none),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩) =
      some ⟨exit, (ambient, none),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩ := by
  have native := SourceTupleResetMachine.resetTrace formula indices id none
    (nativeProgram (width := width) (A := A)) (fun _ => rfl) ambient
  have placed := Placement.trace tape view left right labels exit extra
    (nativeProgram (width := width) (A := A)) program atLabels _ _ _ native
  simpa only [Placement.configuration, Placement.label, entry, SourceTuplePlacement.tapes]
    using placed

def resetInTime (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit, (ambient, none),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩
      (some ⟨exit, (ambient, none),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩)
      (3 * width * ((SourceOccurrenceEncoding.bits formula).length + 1)) where
  steps := SourceTupleResetMachine.steps formula indices
  evals_in_steps := resetTrace tape view left right labels exit program atLabels extra
    formula indices ambient
  steps_le_m := SourceTupleResetMachine.steps_le formula indices

end PerfectCompleteness.SourceTupleResetPlacement


namespace PerfectCompleteness.SourceTupleBodyPlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding

abbrev Shape := CanonicalKeyShape.Shape
abbrev Signs := NormalizationReadMachine.Signs
abbrev Tape (width : Nat) := SourceTupleData.Tape width
abbrev Label (width : Nat) := SourceTuplePlacement.Label width
abbrev ResetLabel (width : Nat) := SourceTupleResetMachine.Label width
abbrev Alphabet {K : Type} (_ : K) := Bool

abbrev Frame (D : Type) := (Option D × (Bool × Option Bool)) × Option Bool
abbrev State (width : Nat) (U D : Type) :=
  ((SourceTupleMachine.State width U × Option D) × (Bool × Option Bool)) × Option Bool

def registers {width : Nat} {U D : Type} :
    (SourceTupleMachine.State width U × Frame D) ≃ State width U D where
  toFun value := (((value.1, value.2.1.1), value.2.1.2), value.2.2)
  invFun value := (value.1.1.1, ((value.1.1.2, value.1.2), value.2))
  left_inv := by rintro ⟨source, ⟨⟨descriptor, comparison⟩, head⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨source, descriptor⟩, comparison⟩, head⟩; rfl

variable {width : Nat} {K Λ U D : Type}

def instruction (tape : Tape width → K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State width U D) :=
  fun label => MachineRegularTable.Lift.statement tape labels exit registers
    (SourceTuplePlacement.nativeProgram label)

def resetInstruction (tape : Tape width → K)
    (labels : ResetLabel width → Λ) (exit : Option Λ) :
    ResetLabel width → TM2.Stmt (Alphabet (K := K)) Λ (State width U D) :=
  fun label => MachineRegularTable.Lift.statement tape labels exit registers
    (SourceTupleResetPlacement.nativeProgram label)

variable [DecidableEq K]

theorem tupleTrace (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width U D))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) (shapes : Fin width → Shape) (signs : Signs) (frame : Frame D) :
    (advance (TM2.step program))^[SourceTupleMachine.steps formula indices (List.finRange width)]
      (some ⟨SourceTuplePlacement.entry labels exit,
        registers (SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs), frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩) =
      some ⟨exit,
        registers (SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩ := by
  have native := SourceTupleMachine.tupleTrace formula indices id none none
    (SourceTuplePlacement.nativeProgram (width := width) (A := U)) (fun _ => rfl)
    ambient shapes signs
  have lifted := MachineRegularTable.Lift.trace tape view left right labels exit registers frame extra
    (SourceTuplePlacement.nativeProgram (width := width) (A := U)) program atLabels _ _ _ native
  simpa only [MachineRegularTable.Lift.configuration, Placement.label,
    SourceTuplePlacement.entry, SourceTuplePlacement.tapes] using lifted

def tupleInTime (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width U D))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) (shapes : Fin width → Shape) (signs : Signs) (frame : Frame D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨SourceTuplePlacement.entry labels exit,
        registers (SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs), frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩
      (some ⟨exit,
        registers (SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩)
      (width * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1))) where
  steps := SourceTupleMachine.steps formula indices (List.finRange width)
  evals_in_steps := tupleTrace tape view left right labels exit program atLabels extra
    formula indices ambient shapes signs frame
  steps_le_m := by
    simpa only [List.length_finRange] using
      SourceTupleMachine.steps_le formula indices (List.finRange width)

theorem resetTrace (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : ResetLabel width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width U D))
    (atLabels : ∀ label, program (labels label) = resetInstruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) (shapes : Fin width → Shape) (signs : Signs) (frame : Frame D) :
    (advance (TM2.step program))^[SourceTupleResetMachine.steps formula indices]
      (some ⟨SourceTupleResetPlacement.entry labels exit,
        registers (SourceClauseReaderMachine.clean (ambient, shapes) signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩) =
      some ⟨exit, registers (SourceClauseReaderMachine.clean (ambient, shapes) signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩ := by
  have native := SourceTupleResetMachine.resetTrace formula indices id none
    (SourceTupleResetPlacement.nativeProgram
      (width := width) (A := (U × (Fin width → Shape)) × Signs)) (fun _ => rfl)
    ((ambient, shapes), signs)
  have lifted := MachineRegularTable.Lift.trace tape view left right labels exit registers frame extra
    (SourceTupleResetPlacement.nativeProgram
      (width := width) (A := (U × (Fin width → Shape)) × Signs))
    program atLabels _ _ _ native
  simpa only [MachineRegularTable.Lift.configuration, Placement.label,
    SourceTupleResetPlacement.entry, SourceTuplePlacement.tapes,
    SourceClauseReaderMachine.clean, NormalizationReadMachine.clean] using lifted

theorem finiteState [Finite U] [Finite D] : Finite (State width U D) := inferInstance

end PerfectCompleteness.SourceTupleBodyPlacement

end OAI
