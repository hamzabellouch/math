import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetQuadratic

namespace OAI

/-! # The reciprocal square-root mass of the selected divisors -/

namespace Ostmann

open scoped BigOperators

theorem sum_reciprocal_sqrt_divisors (Q : Finset ℕ) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) =
      ∏ p ∈ Q, (1 + (Real.sqrt (p : ℝ))⁻¹) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro V _
  have he : (V.toList.prod : ℝ) = ∏ p ∈ V, (p : ℝ) := by simp
  rw [he, Real.sqrt_prod V (fun p _ => Nat.cast_nonneg p), Finset.prod_inv_distrib]

theorem reciprocal_sqrt_divisor_mass_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤
      Real.exp ((Q.card : ℝ) / 1000) := by
  rw [sum_reciprocal_sqrt_divisors]
  calc
    _ ≤ ∏ _p ∈ Q, Real.exp (1 / 1000 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p _; positivity
      · intro p hp
        have hs : (1000 : ℝ) ≤ Real.sqrt (p : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          exact_mod_cast hQ p hp
        have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ (1 / 1000 : ℝ) := by
          simpa only [one_div] using (inv_anti₀ (by norm_num : (0 : ℝ) < 1000) hs)
        have he := Real.add_one_le_exp (1 / 1000 : ℝ)
        linarith
    _ = _ := by rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
