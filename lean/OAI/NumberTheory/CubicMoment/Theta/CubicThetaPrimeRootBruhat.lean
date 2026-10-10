import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhatMatrix

namespace OAI

/-! The literal finite-root Bruhat relation, in the original complex
hyperbolic action and with its cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaPrimeRootElement hp y*cubicThetaPrimeRootWeylElement hp*cubicThetaPrimeRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeRootBruhat hp x y hxy) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/(p:ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = (p:ℂ)*(((1-9*x*y)/p:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeRootElement_translation,cubicThetaPrimeRootElement_translation,
    cubicThetaPrimeRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/(p:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix (p:ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeRootBruhat,cubicThetaPrimeRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp
  all_goals simp only [hthree]
  all_goals ring

theorem cubicThetaPrimeRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeRootElement hp y •
      (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootElement hp x • z)))=
      cubicSymbol p (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeRootBruhat_kubota]

end CubicFirstMoment

end

end OAI
