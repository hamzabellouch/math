import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSections

namespace OAI

/-! The fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the prime residue field. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeRootElement_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp x=
      cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ)) := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let u := cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ))
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
    rw [←cubicThetaPrimeSquareRoot_sq p]
    field_simp [cubicThetaPrimeSquareRoot_ne_zero hp.2.ne_zero]
  change D⁻¹*t*D=u
  calc
    _ = D⁻¹*(t*D) := by group
    _ = D⁻¹*(D*u) := by rw [hD]
    _ = u := by group

lemma cubicThetaPrimeRootElement_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) :
    cubicThetaPrimeRootElement hp (x+y)=
      cubicThetaPrimeRootElement hp x*cubicThetaPrimeRootElement hp y := by
  simp only [cubicThetaPrimeRootElement_translation]
  apply Subtype.ext
  change (!![1,((3*(x+y):Eisenstein):ℂ)/(p:ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)=
    !![1,((3*x:Eisenstein):ℂ)/(p:ℂ);0,1]*!![1,((3*y:Eisenstein):ℂ)/(p:ℂ);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_add,add_div,add_comm]

@[simp] lemma cubicThetaPrimeRootElement_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootElement hp 0=1 := by
  rw [cubicThetaPrimeRootElement_translation]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaTranslationMatrix]

lemma cubicThetaPrimeRootElement_neg {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp (-x)=(cubicThetaPrimeRootElement hp x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←cubicThetaPrimeRootElement_add,neg_add_cancel,cubicThetaPrimeRootElement_zero]

lemma cubicThetaPrimeRootElement_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp (p*x)=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) := by
  rw [cubicThetaPrimeRootElement_translation,cubicThetaPrincipalTranslation_complex]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
