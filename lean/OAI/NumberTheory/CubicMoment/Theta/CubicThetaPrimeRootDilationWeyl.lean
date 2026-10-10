import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootDilationSection

namespace OAI

/-! The once-dilated global subspace is preserved by conjugated Weyl
inversion and is concentrated in the zero root-frequency space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootDilation_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaFullComplex cubicThetaFullInversion*
      cubicThetaPrimeDilation hp.2.ne_zero=cubicThetaFullComplex cubicThetaFullInversion := by
  rw [cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaPrimeDilation hp.2.ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ))*
    (cubicThetaPrimeDilation hp.2.ne_zero : Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaPrimeDilation,cubicThetaInversionMatrix,Matrix.mul_apply,
      Fin.sum_univ_two,cubicThetaPrimeSquareRoot_ne_zero hp.2.ne_zero]

theorem cubicThetaPrimeRootDilation_weyl {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaPrimeRootWeylElement hp=
      cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation hp.2.ne_zero := by
  rw [cubicThetaPrimeRootWeylElement,cubicThetaPrimeAtkinMatrix]
  calc
    _ = (cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaFullComplex cubicThetaFullInversion*
      cubicThetaPrimeDilation hp.2.ne_zero)*cubicThetaPrimeDilation hp.2.ne_zero := by group
    _ = _ := by rw [cubicThetaPrimeRootDilation_inversion hp]

theorem cubicThetaPrimeRootDilationSection_weyl {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootDilationSection hp F)=
      cubicThetaPrimeRootDilationSection hp (cubicThetaInversionSection F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrimeRootWeylElement hp • y))=
    F.val (cubicThetaFullComplex cubicThetaFullInversion • (cubicThetaPrimeDilation hp.2.ne_zero • y))
  rw [←mul_smul,cubicThetaPrimeRootDilation_weyl hp,mul_smul]

theorem cubicThetaPrimeRootDilationSection_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (hk : k≠0) (F : CubicThetaSection) :
    cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootDilationSection hp F)=0 := by
  have he := cubicThetaPrimeRootFourierProjection_product hp k 0
    (cubicThetaPrimeRootDilationSection hp F)
  rw [cubicThetaPrimeRootFourierProjection_zero,cubicThetaPrimeRootDilationSection_average hp F,
    ite_eq_right hk] at he
  exact he

end CubicFirstMoment

end

end OAI
