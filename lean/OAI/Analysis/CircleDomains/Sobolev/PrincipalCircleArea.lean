import OAI.Analysis.CircleDomains.Sobolev.SmoothImageArea
import OAI.Analysis.CircleDomains.Rigidity.PrincipalCircleFlux

namespace OAI

/-! The signed area of the first two principal Laurent terms is computed
exactly; the term linear in the first coefficient cancels. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalLeadingCurve (R : ℝ) (c : ℂ) (t : ℝ) : ℂ :=
    unitCircleParam 0 R t + c/unitCircleParam 0 R t

 theorem principalLeadingCurve_hasDerivAt (R : ℝ) (hR : 0 < R) (c : ℂ) (t : ℝ) :
    HasDerivAt (principalLeadingCurve R c)
      ((unitCircleParam 0 R t-c/unitCircleParam 0 R t)*Complex.I*(2*Real.pi)) t := by
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hd := unitCircleParam_hasDerivAt R t
  have he := hd.add ((hd.inv hn).const_mul c)
  convert he using 1
  · funext s
    simp only [principalLeadingCurve, div_eq_mul_inv, Pi.add_apply, Pi.inv_apply]
  · simp only [unitCircleParam]
    field_simp
    ring

 theorem integral_unit_cos_sq :
    (∫ t in (0 : ℝ)..1, Real.cos (2*Real.pi*t)^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x^2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp only [mul_zero, mul_one, integral_cos_sq, Real.sin_zero, mul_zero,
    Real.sin_two_pi, sub_zero, zero_add, smul_eq_mul]
  field_simp

 theorem principal_leading_circle_area (R : ℝ) (hR : 0 < R) (c : ℂ) :
    signedCurveArea (principalLeadingCurve R c) = Real.pi*R^2-Real.pi*‖c‖^2/R^2 := by
  have hn (t : ℝ) : Complex.normSq (circleMap 0 R t) = R^2 := by
    rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hR]
  have hi (t : ℝ) :
      (principalLeadingCurve R c t).re * (deriv (principalLeadingCurve R c) t).im =
      (2*Real.pi*(R^2-c.re^2/R^2)) * Real.cos (2*Real.pi*t)^2 -
        (4*Real.pi*c.re*c.im/R^2) * (Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) -
        (2*Real.pi*c.im^2/R^2) * Real.sin (2*Real.pi*t)^2 := by
    rw [(principalLeadingCurve_hasDerivAt R hR c t).deriv]
    simp only [principalLeadingCurve, unitCircleParam, Complex.add_re, Complex.sub_re,
      Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, hn,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
      circleMap_zero_re, circleMap_zero_im]
    field_simp [hR.ne']
    ring
  have hs : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)^2) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun t : ℝ => Real.cos (2*Real.pi*t)^2) volume 0 1 :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable _ _
  have hsc : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [signedCurveArea, hi]
  rw [intervalIntegral.integral_sub ((hc.const_mul _).sub (hsc.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_sub (hc.const_mul _) (hsc.const_mul _)]
  simp only [intervalIntegral.integral_const_mul, integral_unit_cos_sq,
    integral_unit_sin_sq, integral_unit_sin_cos, mul_zero, sub_zero]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
