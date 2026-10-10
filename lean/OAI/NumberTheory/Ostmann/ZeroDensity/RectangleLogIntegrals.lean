import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

/-! # The reciprocal integral around a rectangle

These explicit logarithmic primitives fix the orientation and the factor
`2 * pi * I` used by the character contour shift.
-/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

noncomputable def rectangleBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) +
    I * (∫ y in c..d, f (b + y * I)) - I * (∫ y in c..d, f (a + y * I))

theorem reciprocal_horizontal_integral (a b h : ℝ) (hh : h ≠ 0) :
    (∫ x in a..b, ((x : ℂ) + h * I)⁻¹) = log (b + h * I) - log (a + h * I) := by
  have hne (x : ℝ) : (x : ℂ) + h * I ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp only [add_im, ofReal_im, mul_im, I_im, I_re, ofReal_re, mul_one,
      mul_zero, add_zero, zero_add, zero_im] at this
    exact hh this
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + h * I)⁻¹) :=
    (Complex.continuous_ofReal.add continuous_const).inv₀ hne
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro x _
  have hp := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * I)
  have hs : (x : ℂ) + h * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    right
    simpa using hh
  simpa using hp.clog_real hs

theorem reciprocal_vertical_integral_right (x c d : ℝ) (hx : 0 < x) :
    I * (∫ y in c..d, ((x : ℂ) + y * I)⁻¹) =
      log (x + d * I) - log (x + c * I) := by
  have hne (y : ℝ) : (x : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hc : Continuous (fun y : ℝ => I * ((x : ℂ) + y * I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro y _
  have hp := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  have hs : (x : ℂ) + y * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using hx
  simpa [div_eq_mul_inv] using hp.clog_real hs

theorem reciprocal_vertical_integral_left (x c d : ℝ) (hx : x < 0) :
    I * (∫ y in c..d, ((x : ℂ) + y * I)⁻¹) =
      log (-(x + d * I)) - log (-(x + c * I)) := by
  have hne (y : ℝ) : (x : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hc : Continuous (fun y : ℝ => I * ((x : ℂ) + y * I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro y _
  have hp := (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)).neg
  have hs : -((x : ℂ) + y * I) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using neg_pos.mpr hx
  simpa only [Pi.neg_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, one_mul, neg_div_neg_eq, div_eq_mul_inv, inv_neg, neg_mul_neg] using hp.clog_real hs

theorem log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log (-z) = log z - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simpa only [log_im, sub_im, add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero, zero_mul] using arg_neg_eq_arg_sub_pi_of_im_pos hz

theorem log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log (-z) = log z + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simpa only [log_im, sub_im, add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero, zero_mul] using arg_neg_eq_arg_add_pi_of_im_neg hz

theorem rectangleBoundaryIntegral_reciprocal (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (fun z => z⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  rw [rectangleBoundaryIntegral, reciprocal_horizontal_integral a b c hc.ne,
    reciprocal_horizontal_integral a b d hd.ne', reciprocal_vertical_integral_right b c d hb,
    reciprocal_vertical_integral_left a c d ha,
    log_neg_of_im_pos (by simpa using hd), log_neg_of_im_neg (by simpa using hc)]
  ring

end Ostmann

end OAI
