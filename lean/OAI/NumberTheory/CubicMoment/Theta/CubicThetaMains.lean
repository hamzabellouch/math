import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeComparison

namespace OAI

/-! The exact first moment and both fixed-angular main theorems. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem patterson_angularComparison : AngularComparisonStatement :=
  cubicTheta_primeComparison

theorem patterson_angularCancellation : AngularCancellationStatement :=
  angularCancellation_of_comparison patterson_angularComparison
    (angularPrimeModel_isLittleO (fixedAngularPrimeExplicitEstimate_of_primitive primitiveAngularHeckeInput_proved))

theorem patterson_firstMoment : FirstMomentStatement := by
  have hc := patterson_angularComparison 0
  have hp := primeModel_asymptotic_of_PNT primaryPrimePNT_proved
  apply (hc.add hp).congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  have he : primeComparisonCoefficient 0=fun p => gaussAtPrime p-angularPrimeModel 0 p := by
    funext p
    simp only [primeComparisonCoefficient,angularPrimeModel,theta_zero,one_mul]
  change primeCutoffSum (primeComparisonCoefficient 0) X+_=_
  rw [he,primeCutoffSum_sub]
  ring

theorem patterson_mainResults :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  ⟨patterson_firstMoment,patterson_angularComparison,patterson_angularCancellation⟩

end CubicFirstMoment

end

end OAI
