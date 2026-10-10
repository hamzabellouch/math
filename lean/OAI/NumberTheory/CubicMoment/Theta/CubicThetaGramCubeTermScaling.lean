import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKernelIntegralScaling

namespace OAI

/-! Pointwise conductor reduction for each scaled denominator term of the
actual Gram integrand. -/
noncomputable section
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramCubeMultiplier (p d : Eisenstein) : ℂ :=
  (norm (p^3):ℂ)-(if p∣d then 0 else (norm (p^2):ℂ))

theorem cubicThetaGramKloostermanTerm_cube_scale {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0)
    (h k : Eisenstein) (V : C_c(ℝ,ℂ)) {v : ℝ} (hv : 0<v) :
    cubicThetaGramKloostermanTerm (p^3*h) (p^3*k)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) V)
      (p^3*d) (v/‖((p^3:Eisenstein):ℂ)‖)=
      (norm (p^3):ℂ)⁻¹*cubicThetaGramCubeMultiplier p d*
        cubicThetaGramKloostermanTerm h k V d v := by
  have hc0 : p^3*d≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hd0
  have hcC : ((p^3*d:Eisenstein):ℂ)≠0 := fun he => hc0 (Subtype.ext he)
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have he : ((p^3*d:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)=(d:ℂ) := by
    push_cast
    field_simp [hpC]
  rw [cubicThetaGramKloostermanTerm,
    dite_eq_left (And.intro (dvd_mul_of_dvd_right hd (p^3)) hc0),
    cubicThetaKloostermanSum_cube_multiplier hp hd hd0,
    cubicThetaGramKernel_integral_scale _ _ _ (pow_ne_zero _ hp.2.ne_zero) _ hcC hv,
    he,cubicThetaGramKloostermanTerm,dite_eq_left (And.intro hd hd0)]
  simp only [Complex.real_smul,Complex.ofReal_inv,cubicThetaGramCubeMultiplier]
  ring

end CubicFirstMoment

end

end OAI
