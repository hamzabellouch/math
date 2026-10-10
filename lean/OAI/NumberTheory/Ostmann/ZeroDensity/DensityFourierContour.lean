import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteSeriesBridge
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianFubini
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityVerticalPolynomial

namespace OAI

/-! # The exact Fourier scaling of the original finite contour sums -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_fourier_integral_scale (f : ℝ → ℂ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ u : ℝ, f u) = ∫ u : ℝ, f (2 * Real.pi * u) := by
  rw [Measure.integral_comp_mul_left f (2 * Real.pi),
    abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

 theorem densitySquareIntegralTerm_sum_fourier (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      ∫ u : ℝ, densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n)
        ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) := by
  rw [densitySquareIntegralTerm_sum_shift χ s hs S hS c hc hc1,
    density_fourier_integral_scale]

 theorem densityFiniteMellin_original_polynomial (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c t u : ℝ) :
    densityFiniteMellin S (fun n => LSeries.term (densitySquareCoefficient χ)
      (densityVerticalPoint (1 / 2) t) n) ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityCharacterPolynomial S
        (densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c))
        χ.character (t + u) := by
  unfold densityFiniteMellin densityCharacterPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [← density_LSeries_term_add]
  have hp : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hS n hn)
  have he : densityVerticalPoint (1 / 2) t + ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityVerticalPoint (1 / 2 + c) (t + u) := by
    unfold densityVerticalPoint
    push_cast
    ring
  rw [he, LSeries.term_of_ne_zero hp.ne', density_vertical_term _ _ _ n hp]
  unfold densitySquareCoefficient densityVerticalCoeff
  ring

end Ostmann

end OAI
