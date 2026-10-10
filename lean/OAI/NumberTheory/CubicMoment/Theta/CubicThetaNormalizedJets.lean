import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalDerivatives

namespace OAI

/-! Relative derivative formulas used to dominate the differentiated
Eisenstein summands by the original absolutely convergent series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaQuadraticFirst_normalized (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    cubicThetaQuadraticFirst r b x=cubicThetaQuadraticPower r b x*
      (2*r*(x:ℂ)/((x^2+b:ℝ):ℂ)) := by
  have hn := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold cubicThetaQuadraticFirst cubicThetaQuadraticPower
  rw [Complex.cpow_sub r 1 hn,Complex.cpow_one]
  ring

lemma cubicThetaQuadraticSecond_normalized (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    cubicThetaQuadraticSecond r b x=cubicThetaQuadraticPower r b x*
      (2*r/((x^2+b:ℝ):ℂ)+4*r*(r-1)*(x:ℂ)^2/((x^2+b:ℝ):ℂ)^2) := by
  have hn := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold cubicThetaQuadraticSecond cubicThetaQuadraticPower
  rw [Complex.cpow_sub r 1 hn,Complex.cpow_sub r 2 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  ring

lemma cubicThetaVerticalFirst_normalized (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    cubicThetaVerticalFirst s b v=cubicThetaVerticalKernel s b v*
      (s/(v:ℂ)-2*s*(v:ℂ)/((v^2+b:ℝ):ℂ)) := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaVerticalFirst cubicThetaVerticalKernel
  rw [cubicThetaQuadraticFirst_normalized (-s) b v hR,
    Complex.cpow_sub s 1 hn,Complex.cpow_one]
  ring

lemma cubicThetaVerticalSecond_normalized (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    cubicThetaVerticalSecond s b v=cubicThetaVerticalKernel s b v*
      (s*(s-1)/(v:ℂ)^2-(4*s^2+2*s)/((v^2+b:ℝ):ℂ)+
        4*s*(s+1)*(v:ℂ)^2/((v^2+b:ℝ):ℂ)^2) := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have hRn := Complex.ofReal_ne_zero.mpr hR.ne'
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaVerticalSecond cubicThetaVerticalKernel
  rw [cubicThetaQuadraticFirst_normalized (-s) b v hR,
    cubicThetaQuadraticSecond_normalized (-s) b v hR,
    Complex.cpow_sub s 2 hn,Complex.cpow_sub s 1 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
