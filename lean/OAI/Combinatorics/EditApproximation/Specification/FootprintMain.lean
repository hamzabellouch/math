import OAI.Combinatorics.EditApproximation.Specification.ConcreteFootprintBridges
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

def computedQueryTemporaryCellsFootprint (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : ℕ :=
  BitQuery.Footprint.rankedBitMemoCells (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoFootprint source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty

noncomputable def integerAcceptedSpaceTermsFootprint (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : List ℕ :=
  let x := source.map integerSymbolCode
  let y := target.map integerSymbolCode
  [8 * integerPreevaluationWork source target N epsilon,
   2 * integerStoredDataSpace source target,
   computedQuerySetupAllocation N,
   (computedQueryMemoResult x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input).memory.fractionStorage,
   computedQueryTemporaryCellsFootprint x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input,
   computedFamilyCoarseCopyStorage x y N input,
   computedFamilyCoarseArrayCapacity x y N input,
   computedFamilyCoarseScratchCapacity x y N input,
   computedFamilyCoarseControlCapacity x y N input,
   4 * (inputHeight N + (integerParameters N).B + 4),
   integerFinalAllocation source target N input,
   8 * (N + 1)]

noncomputable def integerBinarySpaceFootprint (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => 8 * integerPreevaluationWork source target N epsilon +
        2 * integerStoredDataSpace source target +
        suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)
    | .inr execution => (integerAcceptedSpaceTermsFootprint source target N epsilon
        (computedExecutionAccepted _ _ N execution)).sum
  else 8 * integerPreevaluationWork source target N epsilon +
    2 * integerStoredDataSpace source target +
    suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)

theorem computedQueryTemporaryCellsFootprint_eq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedQueryTemporaryCellsFootprint source target N occurrence symbolBits positionBits input =
      computedQueryTemporaryCells source target N occurrence symbolBits positionBits input := by
  have h : computedQueryMemoFootprint source target N occurrence symbolBits positionBits input =
      (fun key => (computedQueryMemoHeap source target N occurrence symbolBits positionBits input key).footprint) := by
    funext key
    exact (computedQueryMemoHeap_footprint source target N occurrence symbolBits positionBits input key).symm
  unfold computedQueryTemporaryCellsFootprint computedQueryTemporaryCells
  rw [h]
  exact BitQuery.Heap.footprint_rankedBitMemoCells _ _ _ _ _ _ _ _

theorem integerAcceptedSpaceTermsFootprint_eq (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerAcceptedSpaceTermsFootprint source target N epsilon input =
      integerAcceptedSpaceTerms source target N epsilon input := by
  simp only [integerAcceptedSpaceTermsFootprint, integerAcceptedSpaceTerms,
    computedQueryTemporaryCellsFootprint_eq]

theorem integerBinarySpaceFootprint_eq (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinarySpaceFootprint source target N epsilon outcome =
      integerBinarySpace source target N epsilon outcome := by
  simp only [integerBinarySpaceFootprint, integerBinarySpace, integerAcceptedSpaceTermsFootprint_eq]
  rfl

theorem almostLinearEditDistance_main (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
          (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswer source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWork source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpaceFootprint source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  simpa only [integerBinarySpaceFootprint_eq] using
    almostLinearEditDistance epsilon hepsilon _hepsilonOne

end OAI.EditApproximation
