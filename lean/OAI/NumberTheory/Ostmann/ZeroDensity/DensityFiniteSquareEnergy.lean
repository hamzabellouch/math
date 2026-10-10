import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierContour
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelLineBound

namespace OAI

/-! # The original finite square sum bounded by its Gaussian polynomial energy -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem densityHalfGaussian_fourier_scale (u : ℝ) :
    densityHalfGaussian (2 * Real.pi * u) ≤ densityHalfGaussian u := by
  unfold densityHalfGaussian
  apply Real.exp_le_exp.mpr
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have h := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg u)
  nlinarith

 theorem densityFiniteSquare_energy (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2 ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2)) ^ c / c) ^ 2 *
      (∫ u : ℝ, densityHalfGaussian u) * ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S
          (densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c))
          χ.character (t + u)‖ ^ 2 := by
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c)
  let s := densityVerticalPoint (1 / 2) t
  have hs : s.re = 1 / 2 := by simp [s, densityVerticalPoint]
  let M := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
    ((χ.modulus : ℝ) * (|s.im| + 2)) ^ c / c
  have hM : 0 ≤ M := by dsimp [M]; positivity
  rw [densitySquareIntegralTerm_sum_fourier χ s hs S hS c hc hc1]
  have hp : Continuous (fun u : ℝ => ‖densityCharacterPolynomial S a χ.character (t + u)‖) :=
    (((densityCharacterPolynomial_continuous S a χ.character).comp (continuous_const.add continuous_id)).norm)
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  apply density_gaussian_integral_cauchy _ _ M (∑ n ∈ S, ‖a n‖) hp (fun _ => norm_nonneg _)
    (fun u => densityCharacterPolynomial_norm S a χ.character (t + u))
  intro u
  rw [densityFiniteKernel, norm_mul, densityFiniteMellin_original_polynomial χ S hS c t u]
  have hk := densitySquareKernel_short_line χ s hs c (2 * Real.pi * u) hc hc1
  calc
    _ ≤ (M * densityHalfGaussian (2 * Real.pi * u)) * ‖densityCharacterPolynomial S a χ.character (t + u)‖ :=
      mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (densityHalfGaussian_fourier_scale u) hM) (norm_nonneg _)

end Ostmann

end OAI
