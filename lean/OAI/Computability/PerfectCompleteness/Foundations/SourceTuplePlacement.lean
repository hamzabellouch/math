import OAI.Computability.PerfectCompleteness.Machines.SourceTupleMachine
import OAI.Computability.UniqueGames.Machines.MachineCloudPadding

namespace OAI


namespace PerfectCompleteness.SourceTuplePlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition

open MachineCloudPadding

abbrev Tape (width : Nat) := SourceTupleData.Tape width
abbrev Label (width : Nat) := SourceTupleMachine.Label (List.finRange width)
abbrev State (width : Nat) (A : Type) := SourceTupleMachine.State width A
abbrev Shape := CanonicalKeyShape.Shape
abbrev Signs := NormalizationReadMachine.Signs
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {width : Nat} {K Λ A : Type}

def nativeProgram : Label width →
    TM2.Stmt (Alphabet (K := Tape width)) (Label width) (State width A) :=
  SourceTupleMachine.instruction (List.finRange width) id none none

def instruction (tape : Tape width → K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State width A) :=
  fun label => Placement.statement tape labels exit (nativeProgram label)

def entry (labels : Label width → Λ) (exit : Option Λ) : Option Λ :=
  Placement.label labels exit
    (SourceTupleMachine.entry (List.finRange width) id none)

def tapes (view : K → Option (Tape width)) (extra : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) : K → List Bool :=
  Placement.tapes view (SourceTupleData.stacks formula indices prepared) extra

theorem tape_injective (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k) : Function.Injective tape := by
  intro a b same
  have viewed := congrArg view same
  simpa only [left, Option.some.injEq] using viewed

theorem tapes_placed (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k) (extra : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) (k : Tape width) :
    tapes view extra formula indices prepared (tape k) =
      SourceTupleData.stacks formula indices prepared k :=
  Placement.tapes_apply tape view left _ extra k

theorem tapes_complement (view : K → Option (Tape width)) (extra : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) (k : K) (outside : view k = none) :
    tapes view extra formula indices prepared k = extra k := by
  simp only [tapes, Placement.tapes, outside]

theorem tapes_eq_base (tape : Tape width → K) (view : K → Option (Tape width))
    (right : ∀ j k, view j = some k → tape k = j) (base : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool)
    (contents : ∀ k, base (tape k) = SourceTupleData.stacks formula indices prepared k) :
    tapes view base formula indices prepared = base := by
  funext j
  cases viewed : view j with
  | none => simp only [tapes, Placement.tapes, viewed]
  | some k =>
      simp only [tapes, Placement.tapes, viewed]
      rw [← right j k viewed]
      exact (contents k).symm

theorem complement_preserved (view : K → Option (Tape width)) (extra : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (before after : Fin width → Bool) (k : K) (outside : view k = none) :
    tapes view extra formula indices after k = tapes view extra formula indices before k := by
  rw [tapes_complement view extra formula indices after k outside,
    tapes_complement view extra formula indices before k outside]

variable [DecidableEq K]

theorem tupleTrace (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : A) (shapes : Fin width → Shape) (signs : Signs) :
    (advance (TM2.step program))^[SourceTupleMachine.steps formula indices (List.finRange width)]
      (some ⟨entry labels exit,
        SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs),
        tapes view extra formula indices (fun _ => false)⟩) =
      some ⟨exit,
        SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs,
        tapes view extra formula indices (fun _ => true)⟩ := by
  have native := SourceTupleMachine.tupleTrace formula indices id none none
    (nativeProgram (width := width) (A := A)) (fun _ => rfl) ambient shapes signs
  have placed := Placement.trace tape view left right labels exit extra
    (nativeProgram (width := width) (A := A)) program atLabels _ _ _ native
  simpa only [Placement.configuration, Placement.label, entry, tapes] using placed

def tupleInTime (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : A) (shapes : Fin width → Shape) (signs : Signs) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit,
        SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs),
        tapes view extra formula indices (fun _ => false)⟩
      (some ⟨exit,
        SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs,
        tapes view extra formula indices (fun _ => true)⟩)
      (width * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1))) where
  steps := SourceTupleMachine.steps formula indices (List.finRange width)
  evals_in_steps := tupleTrace tape view left right labels exit program atLabels extra
    formula indices ambient shapes signs
  steps_le_m := by
    simpa only [List.length_finRange] using
      SourceTupleMachine.steps_le formula indices (List.finRange width)

theorem finiteState [Finite A] : Finite (State width A) := inferInstance

theorem finiteLabels : Finite (Label width) := inferInstance

omit [DecidableEq K] in
theorem finiteAlphabet (k : K) : Finite (Alphabet k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.SourceTuplePlacement

end OAI
