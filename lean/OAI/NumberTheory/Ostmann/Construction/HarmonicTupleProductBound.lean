import OAI.NumberTheory.Ostmann.Construction.HarmonicTuplePointBound

namespace OAI

/-! # A tuple's actual product controls its original harmonic point mass -/
namespace Ostmann
open scoped Classical BigOperators

theorem harmonicTuple_point_product {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (x : H → P) :
    (∏ h, primeSubsetPrior P (Q h) (x h)) ≤
      (∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹) * (∏ h, (x h : ℝ))⁻¹ := by
  calc
    _ ≤ ∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹ * (x h : ℝ)⁻¹ := by
      apply Finset.prod_le_prod₀ (fun _ _ => primeSubsetPrior_nonneg _ _ _)
      intro h _
      unfold primeSubsetPrior
      split_ifs
      · rw [div_eq_mul_inv, mul_comm]
      · positivity
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem harmonicTuple_point_le_product_lower {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (x : H → P) (lower : ℝ)
    (hlower : 0 < lower) (hprod : lower ≤ ∏ h, (x h : ℝ)) :
    (∏ h, primeSubsetPrior P (Q h) (x h)) ≤
      (∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹) * lower⁻¹ := by
  apply (harmonicTuple_point_product P Q x).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => by positivity))
  exact inv_anti₀ hlower hprod

end Ostmann

end OAI
