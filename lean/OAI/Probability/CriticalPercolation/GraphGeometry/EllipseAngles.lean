import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseBoundary
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseMesh

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def lineAngle (c : Circle) : Real.Angle := ((2*(c : ℂ).arg : ℝ) : Real.Angle)

def boundaryError (phi : ℝ) (c : Circle) : ℝ :=
  (lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)).toReal

lemma circle_arg_re (c : Circle) : Real.cos (c : ℂ).arg=(c : ℂ).re := by
  simpa only [Circle.norm_coe,div_one] using Complex.cos_arg c.coe_ne_zero

lemma circle_arg_im (c : Circle) : Real.sin (c : ℂ).arg=(c : ℂ).im := by
  simpa only [Circle.norm_coe,div_one] using Complex.sin_arg (c : ℂ)

lemma circle_exp_re (phi : ℝ) : (Circle.exp phi : ℂ).re=Real.cos phi := by
  simp only [Circle.coe_exp,Complex.exp_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma circle_exp_im (phi : ℝ) : (Circle.exp phi : ℂ).im=Real.sin phi := by
  simp only [Circle.coe_exp,Complex.exp_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma rotated_major_cos (phi : ℝ) (c : Circle) :
    ((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re=Real.cos ((c : ℂ).arg-phi) := by
  rw [rotated_re,circle_exp_re,circle_exp_im,Real.cos_sub,circle_arg_re,circle_arg_im]
  ring

lemma boundary_error_lt (phi : ℝ) (c : Circle)
    (hc : |((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re|<1/8) :
    |boundaryError phi c|<Real.pi/8 := by
  have he : lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)=
      ((2*((c : ℂ).arg-phi-Real.pi/2) : ℝ) : Real.Angle) := by
    rw [lineAngle,←Real.Angle.coe_sub]
    congr 1
    ring
  have hs : |Real.sin ((c : ℂ).arg-phi-Real.pi/2)|<1/8 := by
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_sub,abs_neg]
    rwa [rotated_major_cos] at hc
  have hh := doubled_angle_le_sine ((c : ℂ).arg-phi-Real.pi/2)
  rw [boundaryError,he]
  exact hh.trans_lt (by nlinarith [Real.pi_pos])

lemma boundary_lift (phi : ℝ) (c : Circle) :
    lineAngle c=((2*phi+Real.pi+boundaryError phi c : ℝ) : Real.Angle) := by
  simp only [Real.Angle.coe_add,boundaryError,Real.Angle.coe_toReal]
  abel

lemma boundary_error_seam (c : Circle) : boundaryError Real.pi c=boundaryError 0 c := by
  unfold boundaryError
  congr 1
  have he : ((2*Real.pi+Real.pi : ℝ) : Real.Angle)=((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,zero_add]
  simp [he]

lemma circle_exp_pi : Circle.exp Real.pi= -(Circle.exp 0) := by
  apply Subtype.ext
  apply Complex.ext
  · simp only [circle_exp_re,Circle.coe_neg,Complex.neg_re,Real.cos_pi,Real.cos_zero]
  · simp only [circle_exp_im,Circle.coe_neg,Complex.neg_im,Real.sin_pi,Real.sin_zero,neg_zero]

lemma diskNormalize_seam (W U s : ℝ) : diskNormalize W U (s,Real.pi)=diskNormalize W U (s,0) := by
  funext z
  change normalize _ W (Circle.exp Real.pi) z=normalize _ W (Circle.exp 0) z
  rw [circle_exp_pi,normalize_neg]
  rfl

lemma diskNormalize_center (W U phi : ℝ) : diskNormalize W U (0,phi)=diskNormalize W U (0,0) := by
  funext z
  simp only [diskNormalize,diskRadius,mul_zero,add_zero,normalize_center]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
