import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootRamanujan
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCount

namespace OAI

/-! The cubic character at the cube modulus is the literal unit detector. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_weight_unit {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) :
    cubicSymbol (p^3) (residueRepresentative (p^3) r)=1 := by
  rw [cubicThetaPrimePowerWeight_inflation hp 2,←MulChar.pow_apply' _ (by decide),cubicResidueChar_cube hp]
  exact MulChar.one_apply (hr.map (residueReduction (dvd_pow_self p (by decide : 3≠0))))

lemma cubicThetaPrimeCubeRoot_weight_nonunit {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : ¬IsUnit r) :
    cubicSymbol (p^3) (residueRepresentative (p^3) r)=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [cubicThetaPrimePowerWeight_inflation hp 2]
  have hz := (cubicTheta_primePower_nonunit_iff hp.2 2 r).mp hr
  rw [hz,MulChar.map_zero]
  norm_num

lemma cubicThetaPrimeCubeRoot_weight_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbol (p^3) (residueRepresentative (p^3) 0)=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [cubicThetaPrimePowerWeight_inflation hp 2,map_zero,MulChar.map_zero]
  norm_num

lemma cubicThetaPrimeCubeRoot_gauss_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 0=
      (norm p:ℂ)^3-(norm p:ℂ)^2 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 0
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*0)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 0 at he
  rw [mul_zero,cubicThetaPrimeFourier_three hp 0,ite_eq_left (dvd_zero p),
    eisenstein_norm_pow,Complex.ofReal_pow] at he
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
