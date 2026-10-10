import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Machines.KeyMetadataMachine
import OAI.Computability.PerfectCompleteness.Machines.SignedTupleCleanupMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.SourceOccurrenceProducerLemmas
import OAI.Computability.PerfectCompleteness.Reduction.ExactPreliminaryTarget

namespace OAI


namespace PerfectCompleteness.NormalizedTarget


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def inputBits (input : NormalizedSourceInput.Input) : List Bool :=
  NormalizedSourceInput.bits input

@[simp] theorem inputBits_eq (input : NormalizedSourceInput.Input) :
    inputBits input = SourceOccurrenceEncoding.bits input.formula := rfl

theorem decode_inputBits (input : NormalizedSourceInput.Input) :
    SourceOccurrenceEncoding.decode (inputBits input) = some input.formula :=
  NormalizedSourceInput.decode_bits input

theorem inputBits_injective : Function.Injective inputBits :=
  NormalizedSourceInput.bits_injective

abbrev SourceTuple (input : NormalizedSourceInput.Input) :=
  Fin (TreeCanonical.locationCount branch n t) →
    Fin (NormalizedSourceInput.clauseCount input)

def tupleQuestion (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input) :=
  SourceQuestionOrder.tupleToQuestion indices

@[simp] theorem tupleQuestion_digits (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    SourceQuestionOrder.questionToTuple (tupleQuestion input indices) = indices :=
  SourceQuestionOrder.questionToTuple_tupleToQuestion indices

def sourceShapes (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape :=
  fun position => SourceClauseReaderMachine.clauseShape
    (SourceTupleData.selectedClause input.formula indices position)

def parsedVariableIDs (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) (slot : Fin 3) : Nat :=
  (SourceTupleData.selectedClause input.formula indices position)[slot].variableIndex.val

@[simp] theorem parsedVariableIDs_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) (slot : Fin 3) :
    parsedVariableIDs input indices position slot =
      ((NormalizedSourceInput.clauses input (indices position)).variable slot).val := rfl

theorem sourceSigns_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    SourceTupleScheduleMachine.sourceSigns input.formula indices =
      MetadataFreeSampler.sourceSigns (NormalizedSourceInput.clauses input)
        (tupleQuestion input indices) := by
  funext leaf coordinate
  rfl

theorem signTuple_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    SourceTupleScheduleMachine.signTuple (sourceShapes input indices) =
      MetadataFreeSampler.sourceSigns (NormalizedSourceInput.clauses input)
        (tupleQuestion input indices) :=
  sourceSigns_eq input indices

theorem numberedSlots_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) :
    TreeCanonical.numberedSlots
        (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input)
          (tupleQuestion input indices)) position =
      KeyMetadataMachine.actualSlot (sourceShapes input indices position)
        (indices position).val (parsedVariableIDs input indices position) := by
  change SourceKeys.slot (NormalizedSourceInput.clauses input)
    (.clause (SourceQuestionOrder.questionToTuple
      (SourceQuestionOrder.tupleToQuestion
        (branch := branch) (n := n) (t := t) indices) position)) = _
  simp only [SourceQuestionOrder.questionToTuple_tupleToQuestion]; rfl

theorem sourceTable_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (prepared : Fin (TreeCanonical.locationCount branch n t) → Bool) :
    SourceTupleData.stacks input.formula indices prepared .table = inputBits input := rfl

theorem digit_counter (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (prepared : Fin (TreeCanonical.locationCount branch n t) → Bool)
    (position : Fin (TreeCanonical.locationCount branch n t)) :
    SourceTupleData.stacks input.formula indices prepared (.digit position) =
      List.replicate (indices position).val true := rfl

theorem variable_counter (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) (slot : Fin 3) :
    SourceTupleData.stacks input.formula indices (fun _ => true) (.variableName position slot) =
      List.replicate (parsedVariableIDs input indices position slot) true := rfl

variable (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ

def construct (input : NormalizedSourceInput.Input) : Instance q :=
  ExactPreliminaryTarget.construct (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

def outputBits (input : NormalizedSourceInput.Input) : List Bool :=
  Encoding.gameBits (construct (t := t) rows repeats hn hbranch hrows δ input)

@[simp] theorem construct_eq (input : NormalizedSourceInput.Input) :
    construct (t := t) rows repeats hn hbranch hrows δ input =
      ExactPreliminaryTarget.construct (t := t) (NormalizedSourceInput.clauses input)
        rows repeats hn hbranch hrows δ := rfl

theorem edge_count (input : NormalizedSourceInput.Input) :
    (construct (t := t) rows repeats hn hbranch hrows δ input).edges.length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q *
        (NormalizedSourceInput.clauseCount input) ^ TreeCanonical.locationCount branch n t :=
  ExactPreliminaryTarget.edge_count (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

local instance leftVertex_fintype (input : NormalizedSourceInput.Input) :
    Fintype (CanonicalGame.LeftVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) := Fintype.ofFinite _

local instance rightVertex_fintype (input : NormalizedSourceInput.Input) :
    Fintype (CanonicalGame.RightVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) := Fintype.ofFinite _

local instance leftLabel_fintype (input : NormalizedSourceInput.Input)
    (x : CanonicalGame.LeftVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) :
    Fintype (CanonicalGame.LeftLabel (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats) x) := Fintype.ofFinite _

local instance rightLabel_fintype (input : NormalizedSourceInput.Input)
    (y : CanonicalGame.RightVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) :
    Fintype (CanonicalGame.RightLabel (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats) y) := Fintype.ofFinite _

theorem value_le (input : NormalizedSourceInput.Input) (hδ : 0 < δ) :
    (construct (t := t) rows repeats hn hbranch hrows δ input).value ≤
      (PreliminarySampler.game (NormalizedSourceInput.clauses input)
        branch n t rows repeats hn hbranch hrows).value + (δ : ℝ) / 3 :=
  ExactPreliminaryTarget.value_le (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ hδ

theorem perfectlyComplete (input : NormalizedSourceInput.Input)
    (satisfiable : input.formula.Satisfiable) :
    PerfectlyComplete (construct (t := t) rows repeats hn hbranch hrows δ input) := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  apply ExactPreliminaryTarget.perfectlyComplete (t := t)
    (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ assignment
  intro occurrence
  exact satisfies _ (List.getElem_mem occurrence.isLt)

theorem outputBits_length_le (input : NormalizedSourceInput.Input) :
    let N := (construct (t := t) rows repeats hn hbranch hrows δ input).edges.length
    (outputBits (t := t) rows repeats hn hbranch hrows δ input).length ≤
      2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) :=
  ExactPreliminaryTarget.encoding_length_le (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

end
end PerfectCompleteness.NormalizedTarget

end OAI
