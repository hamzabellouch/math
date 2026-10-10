import OAI.Analysis.KadisonKastler.StripAverageKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # The mass of the strip contour kernel -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

private theorem inverse_exp_sum (t : ℝ) :
    (Real.exp t + Real.exp (-t))⁻¹ = Real.exp t * (1 + Real.exp t ^ 2)⁻¹ := by
  rw [Real.exp_neg]
  field_simp
  ring

theorem integral_strip_real_kernel {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, (Real.exp (a * t) + Real.exp (-a * t))⁻¹) = Real.pi / (2 * a) := by
  have hbase : (∫ t : ℝ, (Real.exp t + Real.exp (-t))⁻¹) = Real.pi / 2 := by
    simp_rw [inverse_exp_sum]
    have h := integral_comp_exp (fun x : ℝ => (1 + x ^ 2)⁻¹)
    simpa only [smul_eq_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
      sub_zero] using h
  have he := Measure.integral_comp_mul_left
    (fun t : ℝ => (Real.exp t + Real.exp (-t))⁻¹) a
  rw [hbase, abs_of_pos (inv_pos.mpr ha)] at he
  convert he using 1
  · congr 1
    funext t
    rw [neg_mul]
  · simp only [smul_eq_mul]
    ring

theorem integral_stripAverageKernel_zero :
    (∫ t : ℝ, stripAverageKernel Real.pi 0 t) = (1 / 2 : ℂ) := by
  have hreal : (∫ t : ℝ, (Real.exp (Real.pi * t) + Real.exp (-Real.pi * t))⁻¹) =
      (1 / 2 : ℝ) := by
    rw [integral_strip_real_kernel Real.pi_pos]
    field_simp
  have he : (fun t => stripAverageKernel Real.pi 0 t) =
      (fun t : ℝ => (((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t))⁻¹ : ℝ) : ℂ)) := by
    funext t
    simp only [stripAverageKernel, zero_mul, neg_zero, Complex.exp_zero, one_div,
      Complex.ofReal_inv]
  rw [he, integral_complex_ofReal, hreal]
  norm_num

end

end KadisonKastler

end OAI
