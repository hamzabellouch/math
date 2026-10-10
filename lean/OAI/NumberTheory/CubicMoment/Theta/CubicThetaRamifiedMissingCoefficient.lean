import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaObservationScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven

namespace OAI

/-! Agreement of the actual and prescribed coefficients in the first
absent ramified class. The frequency index is exactly -lambda*h. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticCoefficient_ramified_two {h : Eisenstein}
    (hh : ¬lambdaE ∣ h) : cubicThetaArithmeticCoefficient (lambdaE^2*h)=0 := by
  by_cases hc : Nonempty (CubicThetaCoordinates (lambdaE^2*h))
  · let R := Classical.choice hc
    have hp : primary (R.cubePart^3) := by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
    have he := congrArg (emultiplicity lambdaE) R.numerator_eq
    simp only [emultiplicity_mul lambdaE_prime,
      emultiplicity_pow_self_of_prime lambdaE_prime,emultiplicity_eq_zero.mpr hh,
      unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
      primary_lambda_emultiplicity hp,zero_add,add_zero] at he
    have hR : R.order=2 := by exact_mod_cast he.symm
    rw [cubicThetaArithmeticCoefficient_formula R]
    simp only [CubicThetaCoordinates.coefficient,hR]
    norm_num
  · simp only [cubicThetaArithmeticCoefficient,dite_eq_right hc]

theorem cubicThetaNormalizedObservedCoefficient_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaNormalizedObservedCoefficient (lambdaE*h)=0 := by
  simp only [cubicThetaNormalizedObservedCoefficient,cubicThetaObservedWhittakerCoefficient,
    cubicThetaArithmeticFourierResidue_lambda_missing hh,mul_zero,zero_mul,zero_div]

theorem cubicThetaNormalizedObservedCoefficient_lambda_missing_eq
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaNormalizedObservedCoefficient (lambdaE*h)=
      cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE*h)) := by
  rw [cubicThetaNormalizedObservedCoefficient_lambda_missing hh]
  rw [show -lambdaE*(lambdaE*h)=-(lambdaE^2*h) by ring,
    cubicThetaArithmeticCoefficient_even,cubicThetaArithmeticCoefficient_ramified_two hh]

end CubicFirstMoment

end

end OAI
