import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryFinalAnswer
import OAI.Combinatorics.EditApproximation.Binary.IntegerQueryWork

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Binary output conversion, with the explicit equal-string guard. -/
def computedQueryAnswerWithWork (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : List Bool × ℕ :=
  if source = target then ([], source.length + target.length + 1)
  else let result := computedQueryMemoResult source target N occurrence symbolBits positionBits input
    let answer := BinaryFraction.finalAnswerWithWork N result.value
    (answer.1, answer.2 + source.length + target.length + 1)

theorem computedQueryAnswerWithWork_value (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    bitWordValue (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits input).1 =
      if source = target then 0 else integerAnswer N ((computedFamilyResult source target N input).value : ℝ) := by
  have h := congrArg RecursiveMemoResult.value (computedQueryMemoResult_decode source target N occurrence
    symbolBits positionBits input hN hell hf hsize hMass hs ht hp htable)
  change (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value.value =
    (computedFamilyResult source target N input).value at h
  unfold computedQueryAnswerWithWork
  split_ifs
  · rfl
  · dsimp only
    rw [BinaryFraction.finalAnswerWithWork_value, h]

theorem computedQueryAnswerWithWork_cost (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits input).2 ≤
      N + inputHeight N ^ 10 := by
  let H := inputHeight N
  have hH : 64 ≤ H := (by have := two_hundred_le_two_pow_thousand.trans hell; omega :
    64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hpH : 0 < H := by omega
  have hw := computedQueryMemoResult_width source target N occurrence symbolBits positionBits input
    hN hell hf hsize hMass hs ht hp htable
  have hc := BinaryFraction.finalAnswerWithWork_cost N
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value
  have hn := computed_input_size_le_height N
  change _ ≤ H ^ 3 at hw
  change Nat.size N ≤ H at hn
  have hthree : H + 1 ≤ 2 * H ^ 3 := by
    have h := (Nat.le_pow (by decide : 0 < 3) : H ≤ H ^ 3)
    omega
  have hsquare := Nat.pow_le_pow_left (show
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value.width +
      Nat.size N + 1 ≤ 3 * H ^ 3 by omega) 2
  have hcoef : 3600 ≤ H ^ 3 := (by decide : 3600 ≤ (64 : ℕ) ^ 3).trans
    (Nat.pow_le_pow_left hH 3)
  have hfin : (BinaryFraction.finalAnswerWithWork N
      (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value).2 ≤ H ^ 9 := by
    calc
      _ ≤ 400 * (3 * H ^ 3) ^ 2 := hc.trans (Nat.mul_le_mul_left 400 hsquare)
      _ = 3600 * H ^ 6 := by ring
      _ ≤ H ^ 3 * H ^ 6 := Nat.mul_le_mul_right _ hcoef
      _ = H ^ 9 := by ring
  have hu : 1 ≤ H ^ 9 := one_le_pow₀ (by omega)
  have hnext : H ^ 9 + 1 ≤ H ^ 10 := by
    have hh := Nat.mul_le_mul_right (H ^ 9) (show 2 ≤ H by omega)
    rw [show H * H ^ 9 = H ^ 10 by ring] at hh
    omega
  change (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits input).2 ≤ N + H ^ 10
  unfold computedQueryAnswerWithWork
  split_ifs <;> dsimp only <;> omega

end EditApproximation

end OAI
