import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositivePoleScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeArithmeticResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHighSource

namespace OAI

/-! The actual mass residue paired with an arbitrary positive-cutoff
source has precisely the normalized arithmetic Fourier coefficient. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveFourierMass_residue {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    inner ℂ (cubicThetaPositiveFourierMass h W hε hW hsm) cubicThetaArithmeticResidueL2=
      ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
        cubicThetaPositiveRadialTest h W ε (4/3) :=
  cubicThetaPositiveResidue_fourier_observation hh W hε hW

theorem cubicThetaPositiveNormalizedResidue_observation_mul {a h : Eisenstein}
    (ha : a≠0) (hh : h≠0) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    (norm a:ℂ)⁻¹*inner ℂ
        (cubicThetaPositiveFourierMass (a*h)
          (cubicThetaRadialWeightScale ‖(a:ℂ)‖
            (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)
          (div_pos hε (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))))
          (cubicThetaRadialWeightScale_positive_low _ W hW)
          (cubicThetaRadialWeightScale_smooth _ _ W hsm))
        cubicThetaArithmeticResidueL2=
      ((Real.pi:ℂ)/Complex.Gamma (4/3)*cubicThetaPositiveRadialTest h W ε (4/3))*
        ((norm a:ℂ)^(-(1/3:ℂ))*cubicThetaArithmeticFourierResidue (a*h) (4/3)) := by
  rw [cubicThetaPositiveFourierMass_residue (mul_ne_zero ha hh),
    cubicThetaPositivePoleRadialTest_scale ha hh W hε hW]
  have hp := cubicThetaPoleScaling_normalization ha
  linear_combination
    ((Real.pi:ℂ)/Complex.Gamma (4/3)*cubicThetaPositiveRadialTest h W ε (4/3)*
      cubicThetaArithmeticFourierResidue (a*h) (4/3))*hp

end CubicFirstMoment

end

end OAI
