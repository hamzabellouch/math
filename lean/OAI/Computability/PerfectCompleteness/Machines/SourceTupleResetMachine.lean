import OAI.Computability.PerfectCompleteness.Foundations.SourceTupleData
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas

namespace OAI


namespace PerfectCompleteness.SourceTupleResetMachine


open Turing
open UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (σ : Type) := σ × Option Bool

def chosen (width : Nat) : List (Tape width) :=
  (List.finRange width).flatMap (fun position =>
    [.variableName position 0, .variableName position 1, .variableName position 2])

@[simp] theorem chosen_length (width : Nat) : (chosen width).length = 3 * width := by
  have lengthFor (positions : List (Fin width)) :
      (positions.flatMap (fun position =>
        [Tape.variableName position 0, .variableName position 1, .variableName position 2])).length =
        3 * positions.length := by
    induction positions with
    | nil => rfl
    | cons position positions ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons,
          List.length_nil, ih]
        omega
  simpa only [chosen, List.length_finRange] using lengthFor (List.finRange width)

@[simp] theorem table_not_mem_chosen (width : Nat) : Tape.table ∉ chosen width := by
  simp [chosen]

@[simp] theorem digit_not_mem_chosen {width : Nat} (position : Fin width) :
    Tape.digit position ∉ chosen width := by
  simp [chosen]

@[simp] theorem work_not_mem_chosen {width : Nat} (slot : Fin 5) :
    Tape.work slot ∉ chosen width := by
  simp [chosen]

@[simp] theorem variable_mem_chosen {width : Nat} (position : Fin width) (slot : Fin 3) :
    Tape.variableName position slot ∈ chosen width := by
  apply List.mem_flatMap.mpr
  refine ⟨position, by simp, ?_⟩
  fin_cases slot <;> simp

theorem finalTapes_eq {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) :
    MachineDrainMany.finalTapes (chosen width) («stacks» formula indices (fun _ => true)) =
      «stacks» formula indices (fun _ => false) := by
  funext key
  rw [MachineDrainMany.finalTapes_apply]
  cases key with
  | table => simp [«stacks»]
  | digit position => simp [«stacks»]
  | work slot => simp [«stacks»]
  | variableName position slot => simp [«stacks»]

theorem variable_count_le_table (formula : Formula) :
    formula.variables ≤ (SourceOccurrenceEncoding.bits formula).length := by
  rw [SourceOccurrenceEncoding.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem clause_count_le_table (formula : Formula) :
    formula.clauses.length ≤ (SourceOccurrenceEncoding.bits formula).length := by
  rw [SourceOccurrenceEncoding.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem stack_length_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (key : Tape width) :
    («stacks» formula indices (fun _ => true) key).length ≤
      (SourceOccurrenceEncoding.bits formula).length := by
  cases key with
  | table => exact Nat.le_refl _
  | digit position =>
      have bounded := (indices position).isLt
      have countBound := clause_count_le_table formula
      simp only [«stacks», List.length_replicate]
      omega
  | work slot => simp [«stacks»]
  | variableName position slot =>
      have bounded := (selectedClause formula indices position)[slot].variableIndex.isLt
      have countBound := variable_count_le_table formula
      have bound : (selectedClause formula indices position)[slot].variableIndex.val ≤
          (SourceOccurrenceEncoding.bits formula).length := by omega
      simpa [«stacks», NormalizationReadMachine.clauseCounters] using bound

def steps {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) : Nat :=
  MachineDrainMany.steps (chosen width) («stacks» formula indices (fun _ => true))

theorem steps_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) :
    steps formula indices ≤ 3 * width * ((SourceOccurrenceEncoding.bits formula).length + 1) := by
  have bound := MachineDrainMany.steps_le_uniform (chosen width)
    («stacks» formula indices (fun _ => true)) (SourceOccurrenceEncoding.bits formula).length
    (stack_length_le formula indices)
  simpa only [steps, chosen_length] using bound

abbrev Label (width : Nat) := MachineDrainMany.Label (chosen width)

variable {width : Nat} {Λ σ : Type}

def instruction (labels : Label width → Λ) (done : Option Λ) :
    Label width → TM2.Stmt (Alphabet (width := width)) Λ (State σ) :=
  MachineDrainMany.instruction (chosen width) labels done

def entry (labels : Label width → Λ) (done : Option Λ) : Option Λ :=
  MachineDrainMany.entry (chosen width) labels done

theorem resetTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (labels : Label width → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction labels done label)
    (ambient : σ) :
    (advance (TM2.step program))^[steps formula indices]
      (some ⟨entry labels done, (ambient, none), «stacks» formula indices (fun _ => true)⟩) =
      some ⟨done, (ambient, none), «stacks» formula indices (fun _ => false)⟩ := by
  have h := MachineDrainMany.trace (chosen width) labels done program atLabels
    («stacks» formula indices (fun _ => true)) ambient none
  rw [MachineDrainMany.finalRegister_none, finalTapes_eq] at h
  exact h

def resetInTime (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (labels : Label width → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction labels done label)
    (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels done, (ambient, none), «stacks» formula indices (fun _ => true)⟩
      (some ⟨done, (ambient, none), «stacks» formula indices (fun _ => false)⟩)
      (3 * width * ((SourceOccurrenceEncoding.bits formula).length + 1)) where
  steps := steps formula indices
  evals_in_steps := resetTrace formula indices labels done program atLabels ambient
  steps_le_m := steps_le formula indices

theorem finiteState [Finite σ] : Finite (State σ) := inferInstance

theorem finiteAlphabet (key : Tape width) : Finite (Alphabet key) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.SourceTupleResetMachine

end OAI
