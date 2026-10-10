import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResiduePrimarySupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryObservedCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScaledCoefficientReduction

namespace OAI

/-! Every nonconstant coefficient of the actual arithmetic residue is
now the explicit Patterson coefficient times a single scalar. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticBaseScalar : ℂ := cubicThetaNormalizedObservedCoefficient 1/81

lemma cubicThetaCoefficientScalar_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [cubicThetaNormalizedObservedCoefficient_weighted (primary_ne_zero hh),
    cubicThetaWeightedFourierResidue_primary_all hh]
  rw [neg_mul,cubicThetaArithmeticCoefficient_even]
  unfold cubicThetaArithmeticBaseScalar
  rw [cubicThetaNormalizedObservedCoefficient_one]
  ring

theorem cubicThetaCoefficientScalar {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (-lambdaE*h) :=
  cubicThetaScaledCoefficientAgreement_primary cubicThetaArithmeticBaseScalar
    (fun _ hb => cubicThetaCoefficientScalar_primary hb) h hh

end CubicFirstMoment

end

end OAI
