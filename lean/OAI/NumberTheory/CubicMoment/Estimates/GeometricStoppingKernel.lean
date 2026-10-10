import OAI.NumberTheory.CubicMoment.Decomposition.StoppingCoefficientIdentity

namespace OAI

/-! Exact all-label stopping with the original product kernel attached.
The product kernel may include a sharp norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppingSelected_product_remainder {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) (bin : Eisenstein → ℕ) (j : ℕ)
    {t : Finset Eisenstein} (ht : t ⊆ primeBin (primaryPrimeFactors n) bin j) :
    (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
      (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p) = n := by
  exact (primaryFactorRemainder_spec hn hs (stoppingSelected_subset ht)).2.2

/-- The inverse-binomial stopping sum reconstructs the literal original
kernel, without smoothing or changing the product support. -/
theorem geometric_label_stopping_kernel {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ q ∈ stoppingLabelBox ρ X,
      ∑ t ∈ (primeBin (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
        if (primeBin (stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t)
              (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
            (R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
                geometricBinLower ρ X q.1 < Z ∧
              Z ≤ R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
          (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t, p) *
              cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t, p)) *
            K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p)*
              (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p))
        else 0) = cutoffMoebius ψ w n*K n := by
  have hp : ∀ p ∈ primaryPrimeFactors n, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn hp).1
  have hpX : ∀ p ∈ primaryPrimeFactors n, norm p ≤ X := by
    intro p hp
    exact (norm_le_of_dvd (primary_ne_zero hn) (primaryPrimeFactor_spec hn hp).2).trans hnorm
  have hnprod := primaryPrimeFactors_prod hn hs
  have hprod : norm (∏ p ∈ primaryPrimeFactors n, p) ≤ X := by rwa [hnprod]
  have he := congrArg (fun z : ℂ => z*K n)
    (geometric_label_stopping_sum (primaryPrimeFactors n) hp hρ hρ₂ hX hprod hpX
      hR hstart hend ψ w)
  rw [hnprod] at he
  simp_rw [Finset.sum_mul,ite_mul,zero_mul] at he
  refine Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro t ht
  rw [stoppingSelected_product_remainder hn hs _ _ (Finset.mem_powersetCard.mp ht).1]

end CubicFirstMoment

end

end OAI
