import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAction

namespace OAI

/-! The cubic-scale fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the cube modulus. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootElement_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp x=
      cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let u := cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ))
  have hD : D*u=t*D := by
    rw [show t=cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ) from
      cubicThetaPrincipalTranslation_complex x]
    apply Subtype.ext
    change (D:Matrix (Fin 2) (Fin 2) ℂ)*(u:Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ):Matrix (Fin 2) (Fin 2) ℂ)*
        (D:Matrix (Fin 2) (Fin 2) ℂ)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D,u,cubicThetaPrimeDilation,cubicThetaTranslationMatrix,
        Matrix.mul_apply,Fin.sum_univ_two]
    have hs : (p:ℂ)^3=(cubicThetaPrimeSquareRoot (p^3))^2 := by
      have hc : ((p^3:Eisenstein):ℂ)=(p:ℂ)^3 := map_pow eisensteinRing.val p 3
      exact hc.symm.trans (cubicThetaPrimeSquareRoot_sq (p^3)).symm
    rw [hs]
    field_simp [cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)]
  change D⁻¹*t*D=u
  calc
    _ = D⁻¹*(t*D) := by group
    _ = D⁻¹*(D*u) := by rw [hD]
    _ = u := by group

lemma cubicThetaPrimeCubeRootElement_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (x+y)=
      cubicThetaPrimeCubeRootElement hp x*cubicThetaPrimeCubeRootElement hp y := by
  simp only [cubicThetaPrimeCubeRootElement_translation]
  apply Subtype.ext
  change (!![1,((3*(x+y):Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)=
    !![1,((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1]*!![1,((3*y:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_add,add_div,add_comm]

@[simp] lemma cubicThetaPrimeCubeRootElement_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootElement hp 0=1 := by
  rw [cubicThetaPrimeCubeRootElement_translation]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaTranslationMatrix]

lemma cubicThetaPrimeCubeRootElement_neg {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (-x)=(cubicThetaPrimeCubeRootElement hp x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←cubicThetaPrimeCubeRootElement_add,neg_add_cancel,cubicThetaPrimeCubeRootElement_zero]

lemma cubicThetaPrimeCubeRootElement_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p^3*x)=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrincipalTranslation_complex]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

end CubicFirstMoment

end

end OAI
