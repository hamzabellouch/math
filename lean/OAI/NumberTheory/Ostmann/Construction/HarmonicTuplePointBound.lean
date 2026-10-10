import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

/-! # Counterpart point probabilities from the original prime-cell lower endpoints -/

namespace Ostmann
open scoped BigOperators Classical

theorem primeSubsetPrior_le_lower_endpoint (P Q : Finset ℕ) (lo : ℝ) (hlo : 0 < lo)
    (hcell : ∀ p ∈ Q, lo ≤ (p : ℝ)) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * lo⁻¹ := by
  unfold primeSubsetPrior
  split_ifs with hp
  · rw [div_eq_mul_inv, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [one_div] using one_div_le_one_div_of_le hlo (hcell p hp)
  · positivity

/-- The entire ordered tuple has its reciprocal-product scale and exact
harmonic normalizer, with no dependence on the matching permutation. -/
theorem harmonicTuple_point_le {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (lo : H → ℝ)
    (hlo : ∀ h, 0 < lo h) (hcell : ∀ h p, p ∈ Q h → lo h ≤ (p : ℝ))
    (x : H → P) :
    (∏ h, primeSubsetPrior P (Q h) (x h)) ≤
      (∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹) * (∏ h, lo h)⁻¹ := by
  calc
    _ ≤ ∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹ * (lo h)⁻¹ :=
      Finset.prod_le_prod₀ (fun _ _ => primeSubsetPrior_nonneg _ _ _)
        (fun h _ => primeSubsetPrior_le_lower_endpoint P (Q h) (lo h) (hlo h) (hcell h) (x h))
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Ostmann

end OAI
