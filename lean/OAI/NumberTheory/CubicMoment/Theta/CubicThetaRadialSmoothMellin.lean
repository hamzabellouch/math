import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialContour
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedSmoothMellin

namespace OAI

/-! Mellin inversion for the zero angular primary projection, with its
actual radial Dirichlet continuation. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaSelected_smooth_radial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g false 0 W Z=
      ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)*
          cubicThetaSelectedRadialDirichlet g hc ((σ:ℂ)+(t:ℂ)*Complex.I) := by
  have ha (n : Eisenstein) :
      ‖cubicThetaCoefficientTwist cubicThetaSelectedCoefficient (cubicThetaPrimaryCuspCenter g) n‖ ≤ 81 := by
    rw [cubicThetaCoefficientTwist_norm]
    exact cubicThetaSelectedCoefficient_norm n
  simp only [cubicThetaSelectedAdditiveSum,cubicThetaCircleOrder,Bool.not_false,
    ite_true,Nat.cast_zero,neg_zero,theta_zero,one_mul]
  rw [cubicTheta_smooth_mellin (by norm_num) ha W hW hpos hsm hσ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [cubicThetaSelectedRadialDirichlet_initial g hc (by simpa using hσ)]

lemma cubicThetaSelected_smooth_radial_shift (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a Z : ℝ} (ha : a<5/6) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g false 0 W Z=
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
        mellin W ((a:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
          cubicThetaSelectedRadialDirichlet g hc ((a:ℂ)+(t:ℂ)*Complex.I))+
      cubicThetaSelectedRadialResidue g hc*mellin W (5/6)*(Z:ℂ)^(5/6:ℂ) := by
  rw [cubicThetaSelected_smooth_radial g hc W hW hpos hsm (σ:=2) (by norm_num) hZ,
    cubicThetaSelectedRadialDirichlet_contour g hc W hW hpos hsm ha
      (by norm_num : (5/6:ℝ)<2) hZ,mul_add]
  have he : ((1/(2*Real.pi):ℝ):ℂ)*((2*Real.pi:ℝ):ℂ)=1 := by
    push_cast
    field_simp
  rw [←mul_assoc _ ((2*Real.pi:ℝ):ℂ),he,one_mul]

end CubicFirstMoment

end

end OAI
