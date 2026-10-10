import OAI.Analysis.CircleDomains.Topology.RoundDiskGreen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The leading principal Laurent terms give the exact first-order
outward flux on a round circle. Higher-order terms are estimated separately. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_unit_sin_sq :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x^2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero, zero_mul,
    Real.sin_two_pi, sub_zero, mul_zero, zero_add, smul_eq_mul]
  field_simp

 theorem integral_unit_sin_cos :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x*Real.cos x)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp [integral_sin_mul_cos₁, Real.sin_two_pi]

 theorem principal_leading_circle_flux (R : ℝ) (hR : 0 < R) (c : ℂ) :
    planarFormIntegral (fun z => -(z+c/z).im) (fun _ => 0) (unitCircleParam 0 R) =
      Real.pi*R^2-Real.pi*c.re := by
  have hnorm (t : ℝ) : Complex.normSq (circleMap 0 R t) = R^2 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [norm_circleMap_zero, abs_of_pos hR]
  have hi (t : ℝ) :
      -(unitCircleParam 0 R t + c/unitCircleParam 0 R t).im *
        (deriv (unitCircleParam 0 R) t).re + 0 * (deriv (unitCircleParam 0 R) t).im =
      2*Real.pi*R^2 * Real.sin (2*Real.pi*t)^2 +
        2*Real.pi*c.im * (Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) -
        2*Real.pi*c.re * Real.sin (2*Real.pi*t)^2 := by
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    simp only [unitCircleParam, Complex.add_im, Complex.div_im, hnorm, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
      circleMap_zero_re, circleMap_zero_im]
    field_simp [hR.ne']
    ring
  have hs : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)^2) volume 0 1 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2 |>.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [planarFormIntegral, hi]
  rw [intervalIntegral.integral_sub ((hs.const_mul _).add (hc.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_add (hs.const_mul _) (hc.const_mul _)]
  simp only [intervalIntegral.integral_const_mul, integral_unit_sin_sq,
    integral_unit_sin_cos, mul_zero, add_zero]
  ring

end CircleDomainRigidity

end

end OAI
