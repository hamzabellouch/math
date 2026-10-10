import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryExecution
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryWidth
import OAI.Combinatorics.EditApproximation.Binary.BitMemoStorage

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

section Storage
variable (source target : List ℕ) (N : ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (input : ComputedFamilyInput source target N) (hN : 0 < N)
  (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
  (hsize : source.length + target.length ≤ N)
  (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
    (inputHeight N)) ≤ inputHeight N)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_width :
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value.width ≤
      inputHeight N ^ 3 := by
  have h := (rankedBitMemoEvaluate_sound (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hMass)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty
    (bitMemoSound_empty _ _ _)).1
  change (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value = _ at h
  rw [h]
  exact computedQueryMemoNormalized_width source target N occurrence symbolBits positionBits input
    hN (two_hundred_le_two_pow_thousand.trans hell) hf hsize hMass hs ht hp htable _

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_allWidths :
    BinaryMemo.AllValues (fun word => word.width ≤ inputHeight N ^ 3)
      (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory := by
  apply rankedBitMemoEvaluate_widths
    (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hMass)
    (inputHeight N ^ 3)
  · exact computedQueryMemoNormalized_width source target N occurrence symbolBits positionBits input
      hN (two_hundred_le_two_pow_thousand.trans hell) hf hsize hMass hs ht hp htable
  · exact bitMemoSound_empty _ _ _
  · intro key word h
    simp only [BinaryMemo.lookup_empty, reduceCtorEq] at h

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_storage :
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory.fractionStorage ≤
      (N + 2) ^ 65557 := by
  have hw := computedQueryMemoResult_allWidths source target N occurrence symbolBits positionBits
    input hN hell hf hsize hMass hs ht hp htable
  have hs' := BinaryMemo.fractionStorage_le _ (inputHeight N ^ 3) hw
  have hd := congrArg (fun result : RecursiveMemoResult (ComputedFamilyMemoKey source target N) =>
    result.memory.nodes) (computedQueryMemoResult_decode source target N occurrence symbolBits positionBits
      input hN hell hf hsize hMass hs ht hp htable)
  simp only [BitRecursiveMemoResult.decode, BinaryMemo.mapValues_nodes] at hd
  have hn : (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory.nodes ≤
      (N + 2) ^ 65542 := by
    rw [hd]
    exact Nat.le_trans (Nat.le_succ _) (physicalFamilyMemo_nodes_polynomial source target N
      (integerParameters N).P (integerParameters N).T (integerParameters N).S (inputHeight N)
      (Nat.two_pow_pos _) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (finalTargetState target.length) input)
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hh
  change inputHeight N ^ 3 ≤ (N + 2) ^ 12 at hh
  have hu : 1 ≤ (N + 2) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have he : 8 ≤ (N + 2) ^ 3 := (by decide : 8 ≤ (2 : ℕ) ^ 3).trans
    (Nat.pow_le_pow_left (by omega) 3)
  have hc : 2 * inputHeight N ^ 3 + 4 ≤ (N + 2) ^ 15 := by
    calc
      _ ≤ 8 * (N + 2) ^ 12 := by omega
      _ ≤ (N + 2) ^ 3 * (N + 2) ^ 12 := Nat.mul_le_mul_right _ he
      _ = _ := by rw [← pow_add]
  exact hs'.trans ((Nat.mul_le_mul hc hn).trans_eq (by rw [← pow_add]))

end Storage
end EditApproximation

end OAI
