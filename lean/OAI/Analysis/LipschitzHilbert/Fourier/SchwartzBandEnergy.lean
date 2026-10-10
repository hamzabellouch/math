import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The two band-energy inequalities used by the actual cell-average
comparison, proved from Mathlib's Schwartz Plancherel theorem. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem schwartz_fourier_deriv (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ f) ξ =
      (2 * Real.pi * Complex.I * ξ) • 𝓕 f ξ := by
  exact congrFun (Real.fourier_deriv f.integrable f.differentiable
    (SchwartzMap.derivCLM ℂ ℂ f).integrable) ξ

theorem norm_fourier_deriv_coefficient (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem schwartz_band_derivative_upper (f : SchwartzMap ℝ ℂ) {R : ℝ} (_hR : 0 ≤ R)
    (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    (∫ x, ‖deriv f x‖ ^ 2) ≤ (2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : ‖𝓕 df ξ‖ ^ 2 ≤ (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
    by_cases hξ : |ξ| ≤ R
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, ‖𝓕 df ξ‖ ^ 2 := by
      simpa only [df, SchwartzMap.derivCLM_apply] using
        (SchwartzMap.integral_norm_sq_fourier df).symm
    _ ≤ ∫ ξ, (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 :=
      integral_mono (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
        ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]

theorem schwartz_band_derivative_lower (f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hband : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0) :
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖f x‖ ^ 2) ≤ ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 ≤ ‖𝓕 df ξ‖ ^ 2 := by
    by_cases hξ : r ≤ |ξ|
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      simp only [mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
      rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]
    _ ≤ ∫ ξ, ‖𝓕 df ξ‖ ^ 2 :=
      integral_mono ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _)
        (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) hpoint
    _ = _ := by
      simpa only [df, SchwartzMap.derivCLM_apply] using SchwartzMap.integral_norm_sq_fourier df

end LipschitzHilbert

end

end OAI
