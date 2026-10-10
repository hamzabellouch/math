import OAI.Computability.PerfectCompleteness.Foundations.SourceTupleData
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas

namespace OAI


namespace PerfectCompleteness.SourceTupleMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

abbrev Signs := NormalizationReadMachine.Signs
abbrev Shape := CanonicalKeyShape.Shape
abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (width : Nat) (A : Type) := SourceCoordinateMachine.State (A × (Fin width → Shape))

structure Data (width : Nat) where
  prepared : Fin width → Bool
  shapes : Fin width → Shape
  signs : Signs

def state {width : Nat} {A : Type} (ambient : A) (data : Data width) : State width A :=
  SourceClauseReaderMachine.clean (ambient, data.shapes) data.signs

def initial {width : Nat} (shapes : Fin width → Shape) (signs : Signs) : Data width :=
  ⟨fun _ => false, shapes, signs⟩

def update {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width)
    (data : Data width) : Data width where
  prepared := Function.update data.prepared position true
  shapes := Function.update data.shapes position
    (SourceClauseReaderMachine.clauseShape (selectedClause formula indices position))
  signs := NormalizationReadMachine.clauseSigns (selectedClause formula indices position)

def result {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) : List (Fin width) → Data width → Data width
  | [], data => data
  | position :: positions, data => result formula indices positions (update formula indices position data)

def cost {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) : Nat :=
  SourceCoordinateMachine.steps formula (indices position)

def steps {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width)) : Nat :=
  (positions.map (cost formula indices)).sum

theorem result_prepared {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (data : Data width) (position : Fin width) :
    (result formula indices positions data).prepared position =
      if position ∈ positions then true else data.prepared position := by
  induction positions generalizing data with
  | nil => rfl
  | cons first positions ih =>
      rw [result, ih]
      by_cases here : position = first
      · subst position
        simp [update]
      · simp [update, here]

theorem result_shapes {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (data : Data width) (position : Fin width) :
    (result formula indices positions data).shapes position =
      if position ∈ positions then
        SourceClauseReaderMachine.clauseShape (selectedClause formula indices position)
      else data.shapes position := by
  induction positions generalizing data with
  | nil => rfl
  | cons first positions ih =>
      rw [result, ih]
      by_cases here : position = first
      · subst position
        simp [update]
      · simp [update, here]

theorem result_finRange_prepared {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) :
    (result formula indices (List.finRange width) data).prepared = fun _ => true := by
  funext position
  simp [result_prepared]

theorem result_finRange_shapes {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) :
    (result formula indices (List.finRange width) data).shapes =
      fun position => SourceClauseReaderMachine.clauseShape
        (selectedClause formula indices position) := by
  funext position
  simp [result_shapes]

theorem cost_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) :
    cost formula indices position ≤ 60 * ((SourceOccurrenceEncoding.bits formula).length + 1) := by
  have bound := SourceCoordinateMachine.steps_le formula (indices position)
  have indexBound := (indices position).isLt
  have countBound : formula.clauses.length ≤ (SourceOccurrenceEncoding.bits formula).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  unfold cost
  omega

theorem steps_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width)) :
    steps formula indices positions ≤
      positions.length * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1)) := by
  induction positions with
  | nil => simp [steps]
  | cons position positions ih =>
      have head := cost_le formula indices position
      simp only [steps, List.map_cons, List.sum_cons, List.length_cons] at *
      calc
        _ ≤ 60 * ((SourceOccurrenceEncoding.bits formula).length + 1) +
            positions.length * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1)) :=
          Nat.add_le_add head ih
        _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

abbrev LocalLabel {width : Nat} (_ : Fin width) := SourceCoordinateMachine.Label
abbrev Label {width : Nat} (positions : List (Fin width)) :=
  MachineFiniteSequence.Label LocalLabel positions

def localMain {width : Nat} (_ : Fin width) : SourceCoordinateMachine.Label :=
  SourceCoordinateMachine.main

def save {width : Nat} {A : Type} (position : Fin width)
    (ambient : A × (Fin width → Shape)) (shape : Shape) : A × (Fin width → Shape) :=
  (ambient.1, Function.update ambient.2 position shape)

variable {width : Nat} {Λ A : Type}

def localInstruction (rejected : Option Λ) (position : Fin width)
    (labels : SourceCoordinateMachine.Label → Λ) (done : Option Λ) :
    SourceCoordinateMachine.Label → TM2.Stmt (Alphabet (width := width)) Λ (State width A) :=
  SourceCoordinateMachine.instruction (localTape position) labels done rejected (save position)

def instruction (positions : List (Fin width)) (labels : Label positions → Λ)
    (done rejected : Option Λ) :
    Label positions → TM2.Stmt (Alphabet (width := width)) Λ (State width A) :=
  MachineFiniteSequence.instruction LocalLabel localMain
    (localInstruction rejected) positions labels done

def entry (positions : List (Fin width)) (labels : Label positions → Λ) (done : Option Λ) :
    Option Λ := MachineFiniteSequence.entry LocalLabel localMain positions labels done

theorem sequenceTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (nodup : positions.Nodup) (labels : Label positions → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) = instruction positions labels done rejected label)
    (ambient : A) (data : Data width)
    (fresh : ∀ position ∈ positions, data.prepared position = false) :
    (advance (TM2.step program))^[steps formula indices positions]
      (some ⟨entry positions labels done, state ambient data,
        «stacks» formula indices data.prepared⟩) =
      some ⟨done, state ambient (result formula indices positions data),
        «stacks» formula indices (result formula indices positions data).prepared⟩ := by
  induction positions generalizing data with
  | nil => rfl
  | cons position positions ih =>
      have distinct := List.nodup_cons.mp nodup
      have headFresh := fresh position (by simp)
      let tailEntry := entry positions (fun label => labels (.inr label)) done
      have first := SourceCoordinateMachine.coordinateTrace (localTape position)
        (localTape_injective position) (fun label => labels (.inl label)) tailEntry rejected
        (save position) program (fun label => atLabels (.inl label))
        («stacks» formula indices data.prepared) (ambient, data.shapes)
        formula (indices position) data.signs rfl rfl
        (coordinate_initial_empty formula indices data.prepared position headFresh)
      have outputTapes := resultTapes_eq formula indices data.prepared position headFresh
      dsimp only [selectedClause] at outputTapes
      rw [outputTapes] at first
      change (advance (TM2.step program))^[cost formula indices position]
        (some ⟨some (labels (.inl SourceCoordinateMachine.main)), state ambient data,
          «stacks» formula indices data.prepared⟩) =
        some ⟨tailEntry, state ambient (update formula indices position data),
          «stacks» formula indices (update formula indices position data).prepared⟩ at first
      have tailFresh : ∀ next ∈ positions,
          (update formula indices position data).prepared next = false := by
        intro next member
        have different : next ≠ position := by
          intro same
          subst next
          exact distinct.1 member
        simpa only [update, Function.update_of_ne different] using
          fresh next (List.mem_cons_of_mem position member)
      have rest := ih distinct.2 (fun label => labels (.inr label))
        (fun label => atLabels (.inr label)) (update formula indices position data) tailFresh
      rw [steps, List.map_cons, List.sum_cons, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps formula indices positions]
        ((advance (TM2.step program))^[cost formula indices position]
          (some ⟨some (labels (.inl SourceCoordinateMachine.main)), state ambient data,
            «stacks» formula indices data.prepared⟩)) = _
      rw [first]
      exact rest

theorem tupleTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (labels : Label (List.finRange width) → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) =
      instruction (List.finRange width) labels done rejected label)
    (ambient : A) (shapes : Fin width → Shape) (signs : Signs) :
    (advance (TM2.step program))^[steps formula indices (List.finRange width)]
      (some ⟨entry (List.finRange width) labels done, state ambient (initial shapes signs),
        «stacks» formula indices (fun _ => false)⟩) =
      some ⟨done,
        SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (selectedClause formula indices position))
          (result formula indices (List.finRange width) (initial shapes signs)).signs,
        «stacks» formula indices (fun _ => true)⟩ := by
  have traced := sequenceTrace formula indices (List.finRange width) (List.nodup_finRange width)
    labels done rejected program atLabels ambient (initial shapes signs) (by intros; rfl)
  simpa only [state, initial, result_finRange_prepared, result_finRange_shapes] using traced

def tupleInTime (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (labels : Label (List.finRange width) → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) =
      instruction (List.finRange width) labels done rejected label)
    (ambient : A) (shapes : Fin width → Shape) (signs : Signs) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry (List.finRange width) labels done, state ambient (initial shapes signs),
        «stacks» formula indices (fun _ => false)⟩
      (some ⟨done,
        SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (selectedClause formula indices position))
          (result formula indices (List.finRange width) (initial shapes signs)).signs,
        «stacks» formula indices (fun _ => true)⟩)
      (width * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1))) where
  steps := steps formula indices (List.finRange width)
  evals_in_steps := tupleTrace formula indices labels done rejected program atLabels ambient shapes signs
  steps_le_m := by
    simpa only [List.length_finRange] using
      (steps_le formula indices (List.finRange width))

theorem finiteState [Finite A] : Finite (State width A) := inferInstance

theorem finiteLabels : Finite (Label (List.finRange width)) := inferInstance

end PerfectCompleteness.SourceTupleMachine

end OAI
