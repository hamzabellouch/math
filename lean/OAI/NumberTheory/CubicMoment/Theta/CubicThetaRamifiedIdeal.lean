import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDensityLocal

namespace OAI

/-! The single ramified ideal in the cube part of the constant term. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedPrime : EisensteinIdealPrime :=
  ⟨Associates.mk lambdaE,Associates.irreducible_mk.mpr lambdaE_prime.irreducible⟩

lemma cubicThetaRamifiedPrime_associated :
    Associated (idealPrimeRepresentative cubicThetaRamifiedPrime) lambdaE := by
  apply Associates.mk_eq_mk_iff_associated.mp
  exact Associates.quotient_out _

lemma cubicThetaRamifiedPrime_norm : normNat (idealPrimeRepresentative cubicThetaRamifiedPrime)=3 := by
  rw [associated_normNat cubicThetaRamifiedPrime_associated]
  apply Nat.cast_injective (R:=ℝ)
  rw [normNat_cast]
  exact traceLambda_normSq

lemma cubicTheta_lambda_exponent : idealExponentOf lambdaE=Finsupp.single cubicThetaRamifiedPrime 1 := by
  rw [←idealExponentOf_primeRepresentative cubicThetaRamifiedPrime]
  exact (idealExponentOf_eq_of_associated
    (idealPrimeRepresentative_irreducible cubicThetaRamifiedPrime).ne_zero lambdaE_prime.ne_zero
    cubicThetaRamifiedPrime_associated).symm

lemma cubicThetaRamifiedPrime_dvd_iff (ν : EisensteinIdealExponent) :
    lambdaE∣idealExponentGenerator ν ↔ 0<ν cubicThetaRamifiedPrime := by
  rw [←cubicThetaRamifiedPrime_associated.dvd_iff_dvd_left,
    idealPrime_dvd_iff (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]

lemma cubicThetaSignedCube_ramified (ε : Bool) (ν : EisensteinIdealExponent) :
    (3:Eisenstein)∣cubicThetaSignedCube ε ν ↔ 0<ν cubicThetaRamifiedPrime := by
  cases ε <;> simp only [cubicThetaSignedCube,Bool.false_eq_true,ite_true,ite_false]
  · rw [cubicTheta_cube_row_three_iff,cubicThetaRamifiedPrime_dvd_iff]
  · rw [dvd_neg,cubicTheta_cube_row_three_iff,cubicThetaRamifiedPrime_dvd_iff]

end CubicFirstMoment

end

end OAI
