import OAI.NumberTheory.CubicMoment.Estimates.PrimeSubsetNormTail

namespace OAI

/-! Restricted versions of the convergent prime-subset norm sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_prime_subset_harmonic_on (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {b η : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hbound : ∀ s ∈ A, norm (∏ p ∈ s,p) ≤ b) :
    (∑ s ∈ A, norm (∏ p ∈ s,p)^(-1:ℝ)) ≤
      b^η*(∑' n : Eisenstein, norm n^(-(1+η))) := by
  apply le_trans _ (primary_prime_subset_harmonic U hU hb hη)
  simp only [Real.rpow_neg_one]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact Finset.mem_filter.mpr ⟨hA hs,hbound s hs⟩
  · intro s _ _
    exact inv_nonneg.mpr (norm_nonneg _)

lemma primary_prime_subset_tail_on (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ s ∈ A, D < norm (∏ p ∈ s,p)) :
    (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  apply le_trans _ (primary_prime_subset_norm_tail U hU hD)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact Finset.mem_filter.mpr ⟨hA hs,hbound s hs⟩
  · intro s _ _
    exact Real.rpow_nonneg (norm_nonneg _) _

end CubicFirstMoment

end

end OAI
