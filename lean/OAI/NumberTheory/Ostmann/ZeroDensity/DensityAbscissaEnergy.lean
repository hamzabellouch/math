import OAI.NumberTheory.Ostmann.ZeroDensity.DensityAbscissaPolynomial

namespace OAI

/-! # Coefficient energy decreases to the right of the density line -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem densityVerticalCoeff_norm_mono (a : ℕ → ℂ) (σ x : ℝ) (hx : σ ≤ x)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖densityVerticalCoeff a x n‖ ≤ ‖densityVerticalCoeff a σ n‖ := by
  have hp : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [densityVerticalCoeff_norm a x n hp, densityVerticalCoeff_norm a σ n hp]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by positivity) σ)
    (Real.rpow_le_rpow_of_exponent_le hnR hx)

 theorem density_abscissa_energy_mono (N : ℕ) (a : ℕ → ℂ) (σ x : ℝ) (hx : σ ≤ x) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a x n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact pow_le_pow_left₀ (norm_nonneg _) (densityVerticalCoeff_norm_mono a σ x hx n (Finset.mem_Icc.mp hn).1) 2

 theorem density_abscissa_derivative_energy (N : ℕ) (a : ℕ → ℂ) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n‖ ^ 2) ≤
      (Real.log (N + 1 : ℕ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlN : Real.log n ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).2; omega : n ≤ N + 1))
  have he : densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n =
      -(Real.log n : ℂ) * densityVerticalCoeff a σ n := by
    unfold densityVerticalCoeff densityAbscissaDerivativeCoeff
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl hlN 2) (sq_nonneg _)

end Ostmann

end OAI
