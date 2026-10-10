import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareKernel
import Mathlib.Analysis.Fourier.Inversion

namespace OAI

/-! The exact Cauchy Fourier kernel follows by Fourier inversion from
the exponential transform already used in the mean-square bound. -/

namespace TwoPointCorrelations

open Complex MeasureTheory FourierTransform
open scoped RealInnerProductSpace

noncomputable def mrtLaplaceWeight (x : ℝ) : ℂ := (Real.exp (-|x|) : ℂ)

lemma mrtLaplaceWeight_integrable : Integrable mrtLaplaceWeight := by
  convert mrtMeanSquareKernel_integrable (by norm_num : (0 : ℝ) < 1) 0 using 1
  ext x
  simp [mrtLaplaceWeight, mrtMeanSquareKernel]

lemma mrtLaplaceWeight_continuous : Continuous mrtLaplaceWeight := by
  unfold mrtLaplaceWeight
  fun_prop

theorem mrt_laplace_fourier (t : ℝ) :
    𝓕 mrtLaplaceWeight t = ((2 / (1 + (2 * Real.pi * t) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ =>
      Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) • mrtLaplaceWeight x) =
      mrtMeanSquareKernel 1 (-2 * Real.pi * t) := by
    funext x
    simp only [mrtLaplaceWeight, mrtMeanSquareKernel, div_one, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  rw [he, integral_mrtMeanSquareKernel (by norm_num : (0 : ℝ) < 1)]
  congr 1
  ring

lemma mrtLaplaceWeight_fourier_integrable : Integrable (𝓕 mrtLaplaceWeight) := by
  have hh := (integrable_inv_one_add_mul_sq
    (show (2 : ℝ) * Real.pi ≠ 0 by positivity)).const_mul 2
  convert hh.ofReal using 1
  funext t
  rw [mrt_laplace_fourier]
  congr 1

noncomputable def mrtCauchyKernel (ω t : ℝ) : ℂ :=
  Complex.exp ((ω * t : ℝ) * Complex.I) * ((1 + t ^ 2)⁻¹ : ℝ)

lemma mrtCauchyKernel_integrable (ω : ℝ) : Integrable (mrtCauchyKernel ω) := by
  apply Integrable.mono' integrable_inv_one_add_sq
  · unfold mrtCauchyKernel
    fun_prop
  · filter_upwards with t
    simp only [mrtCauchyKernel, norm_mul, Complex.norm_exp, mul_re,
      ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      Real.exp_zero, one_mul]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 + t ^ 2)⁻¹)]

theorem integral_mrtCauchyKernel (ω : ℝ) :
    (∫ t : ℝ, mrtCauchyKernel ω t) =
      ((Real.pi * Real.exp (-|ω|) : ℝ) : ℂ) := by
  have hi := mrtLaplaceWeight_integrable.fourierInv_fourier_eq
    mrtLaplaceWeight_fourier_integrable (mrtLaplaceWeight_continuous.continuousAt (x := ω))
  rw [Real.fourierInv_eq'] at hi
  simp_rw [mrt_laplace_fourier] at hi
  have he : (fun t : ℝ =>
      Complex.exp ((2 * Real.pi * ⟪t, ω⟫ : ℝ) * Complex.I) •
        ((2 / (1 + (2 * Real.pi * t) ^ 2) : ℝ) : ℂ)) =
      fun t : ℝ => (2 : ℂ) * mrtCauchyKernel ω (2 * Real.pi * t) := by
    funext t
    have ha : (2 * Real.pi * ⟪t, ω⟫ : ℝ) = ω * (2 * Real.pi * t) := by
      rw [Real.inner_apply]
      ring
    rw [ha]
    simp only [smul_eq_mul, mrtCauchyKernel]
    push_cast
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr (show (0 : ℝ) < 2 * Real.pi by positivity)),
    Complex.real_smul] at hi
  dsimp [mrtLaplaceWeight] at hi
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at hi ⊢
  field_simp at hi
  exact hi

end TwoPointCorrelations

end OAI
