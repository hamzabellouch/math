import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroHeat
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! A height dilation turns the weighted heat coefficient into one
Mellin kernel, independent of the spectral parameter. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaLinearHeat (v A u : ℝ) : ℂ :=
  (Real.exp (-v*u-A*v/u):ℂ)

lemma cubicThetaLinearHeat_scale {v t : ℝ} (hv : 0<v) (ht : 0<t)
    (A : ℝ) (s : ℂ) :
    (v:ℂ)^s*cubicThetaDualHeat v s A t=
      (v:ℂ)^2*((v*t:ℝ):ℂ)^(s-2)*cubicThetaLinearHeat v A (v*t) := by
  have he : -v*(v*t)-A*v/(v*t) = -v^2*t-A/t := by field_simp
  have hp : (v:ℂ)^2*(v:ℂ)^(s-2)=(v:ℂ)^s := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  unfold cubicThetaDualHeat cubicThetaLinearHeat
  rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hv.le ht.le]
  rw [← mul_assoc ((v:ℂ)^2) ((v:ℂ)^(s-2)),hp]
  ring

lemma cubicThetaHeat_height_dilation {v : ℝ} (hv : 0<v) (A : ℝ) (s : ℂ) :
    (v:ℂ)^s*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)=
      (v:ℂ)*(∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u) := by
  let g := fun u : ℝ => (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u
  have hi := integral_comp_mul_left_Ioi g 0 hv
  rw [mul_zero] at hi
  calc
    _ = (v:ℂ)^2*(∫ t in Ioi (0:ℝ), g (v*t)) := by
      rw [← integral_const_mul,← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [g]
      simpa only [mul_assoc] using cubicThetaLinearHeat_scale hv ht A s
    _ = _ := by
      rw [hi,Complex.real_smul,Complex.ofReal_inv]
      dsimp only [g]
      field_simp

end CubicFirstMoment

end

end OAI
