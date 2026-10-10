import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaObservationScaling

namespace OAI

/-! The actual normalized Whittaker coefficients agree with the explicit
primary theta family up to its single base coefficient. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaObservedBaseFactor : ℂ :=
  cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    ((2*(cubicThetaRowHeatScale 1)^(1/6:ℝ)/‖cubicThetaRowFrequency 1‖:ℝ):ℂ)/
      ((9*Real.sqrt 3/2:ℝ):ℂ)

lemma cubicThetaNormalizedObservedCoefficient_weighted {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaObservedBaseFactor*cubicThetaWeightedFourierResidue h := by
  have hw := cubicThetaPoleWeight_mul hh (one_ne_zero : (1:Eisenstein)≠0)
  rw [mul_one] at hw
  have hc : (((norm h)^(-(1/3:ℝ)):ℝ):ℂ)=((norm h:ℂ)^(-(1/3:ℂ))) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (norm_nonneg h) (-(1/3:ℝ)))
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    cubicThetaObservedBaseFactor cubicThetaWeightedFourierResidue
  rw [hw,Complex.ofReal_mul,hc]
  ring

lemma cubicThetaNormalizedObservedCoefficient_one :
    cubicThetaNormalizedObservedCoefficient 1=
      cubicThetaObservedBaseFactor*cubicThetaWeightedFourierResidue 1 :=
  cubicThetaNormalizedObservedCoefficient_weighted one_ne_zero

theorem cubicThetaNormalizedObservedCoefficient_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaNormalizedObservedCoefficient (c*d^3)=
      (cubicThetaArithmeticCoefficient (lambdaE*c*d^3)/81)*
        cubicThetaNormalizedObservedCoefficient 1 := by
  rw [cubicThetaNormalizedObservedCoefficient_weighted
    (mul_ne_zero (primary_ne_zero hc) (pow_ne_zero 3 (primary_ne_zero hd))),
    cubicThetaWeightedFourierResidue_theta_primary hc hd hs,
    cubicThetaNormalizedObservedCoefficient_one]
  ring

end CubicFirstMoment

end

end OAI
