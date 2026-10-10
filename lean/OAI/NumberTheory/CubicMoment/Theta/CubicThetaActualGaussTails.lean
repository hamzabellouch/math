import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialGaussTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussTail
import OAI.NumberTheory.CubicMoment.Estimates.HeckeDischargedMains

namespace OAI

/-! The literal Gauss height tail in every fixed angular mode. All inputs
in these tail estimates have now been proved, including the radial pole
with its actual constant; no normalization of that pole is assumed. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem cubicTheta_primeProductGaussTail_isLittleO (ℓ : ℤ) :
    ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
      (fun X => primeProductGaussTail ℓ (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact cubicTheta_primeProductGaussTail_radial_isLittleO primaryPrimePNT_proved
      primitiveResidueHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (fun _ => gammaInverseFiniteOrder _ _)
      (fun _ => by
        simpa only [GammaQuotientStripBound, AngularGammaQuotientStripBound,
          gammaFEQuotient, angularGammaFEQuotient, Complex.ofReal_zero, add_zero] using
          angularGammaQuotientStripBound_proved 0 _ (by norm_num))
  · exact primeProductGaussTail_angular_isLittleO_proved ℓ hℓ primaryPrimePNT_proved
      primitiveAngularHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (fun _ => gammaInverseFiniteOrder _ _)
      (fun _ => angularGammaQuotientStripBound_proved _ _ (by
        linarith [abs_nonneg (ℓ:ℝ)]))

end CubicFirstMoment

end

end OAI
