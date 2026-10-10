import OAI.Analysis.MutuallyUnbiased.MixedMerge.Block76

namespace OAI

namespace MUB6.Certificate.MixedData

theorem finalMergeCheck : merged2423 = merged2452 := by decide +kernel

theorem targetExpressionCheck : expr2452 = targetCombination := by rfl

theorem mergeConsequence (x : Fin 3237 → ℝ) (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) :
    Integer.Combination.eval targetRows x rawCombination = Integer.Combination.eval targetRows x residualCombination := by
  have hz := mergedZero2423 x h
  rw [finalMergeCheck, mergedEval2452, targetExpressionCheck] at hz
  simp only [targetCombination, Integer.Combination.eval, Int.cast_neg, Int.cast_one, neg_one_mul] at hz
  linarith

end MUB6.Certificate.MixedData

end OAI
