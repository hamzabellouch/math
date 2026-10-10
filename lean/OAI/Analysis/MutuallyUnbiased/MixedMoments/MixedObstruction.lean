import OAI.Analysis.MutuallyUnbiased.MixedMerge.Main
import OAI.Analysis.MutuallyUnbiased.Certificate.MixedResidual
import OAI.Analysis.MutuallyUnbiased.Certificate.GramNonnegative

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedData

/-- The checked integer identity is incompatible with a nonnegative Gram
expression and the actual uniform moment bounds. -/
theorem false_of_certificate (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
    (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
    (hnonneg : 0 ≤ Integer.Combination.eval targetRows x rawCombination) : False := by
  have h := mergeConsequence x hsources
  have hneg := residualNegative x hx hzero
  rw [← h] at hneg
  exact (not_lt_of_ge hnonneg) hneg

/-- A bridge to the exact, positively scaled six Gram forms discharges the
nonnegativity premise without any numerical oracle. -/
theorem false_of_gram_interpretation (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
    (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
    (hgram : Integer.Combination.eval targetRows x rawCombination =
      (denominator : ℝ) * GramNonnegative.sourceGram B) : False := by
  apply false_of_certificate x hx hzero hsources
  rw [hgram]
  exact mul_nonneg (by exact_mod_cast denominator_pos.le)
    (GramNonnegative.sourceGram_nonneg B hB)

end MUB6.Certificate.MixedData

end

end OAI
