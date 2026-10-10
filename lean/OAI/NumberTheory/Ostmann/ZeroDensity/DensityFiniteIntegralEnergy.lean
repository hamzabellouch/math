import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelLineBound

namespace OAI

/-! # The square of a finite contour integral at its true short-line cost -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem densityFiniteKernel_integral_energy (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖∫ u : ℝ, densityFiniteKernel χ s S a ((c : ℂ) + u * I)‖ ^ 2 ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2)) ^ c / c) ^ 2 *
      (∫ u : ℝ, densityHalfGaussian u) *
        ∫ u : ℝ, densityHalfGaussian u * ‖densityFiniteMellin S a ((c : ℂ) + u * I)‖ ^ 2 := by
  have hcont : Continuous (fun u : ℝ => ‖densityFiniteMellin S a ((c : ℂ) + u * I)‖) := by
    apply Continuous.norm
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (densityFiniteMellin_analytic S a hS _).continuousAt.comp (by fun_prop)
  apply density_gaussian_integral_cauchy _ _ _ (∑ n ∈ S, ‖a n‖) hcont
    (fun u => norm_nonneg _) _ _
  · intro u
    exact densityFiniteMellin_norm S a hS _ (by simp; linarith)
  · intro u
    rw [densityFiniteKernel, norm_mul]
    exact mul_le_mul_of_nonneg_right (densitySquareKernel_short_line χ s hs c u hc hc1)
      (norm_nonneg _)

end Ostmann

end OAI
