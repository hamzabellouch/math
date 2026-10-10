import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryAnswer

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- The binary evaluator returns exactly the answer used in the execution-law theorem. -/
theorem computedQueryAnswerWithWork_execution (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (execution : ComputedExecutionOutcome source target N) :
    bitWordValue (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits
      (computedExecutionAccepted source target N execution)).1 =
      computedFullAnswer source target N (.inr execution) := by
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlarge.2.1.1
    omega
  rw [computedQueryAnswerWithWork_value source target N occurrence symbolBits positionBits _
    (largeAccuracyInput_pos N epsilon.value hlarge.2.1) hlarge.2.1.1 hf hsize hlarge.2.2 hs ht hp htable]
  change _ = physicalFamilyMemoAnswer source target N (integerParameters N).P (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (finalTargetState target.length) (computedExecutionAccepted source target N execution)
  simp only [physicalFamilyMemoAnswer, finalTargetState, substring, List.drop_zero, List.take_length,
    computedFamilyResult]

end EditApproximation

end OAI
