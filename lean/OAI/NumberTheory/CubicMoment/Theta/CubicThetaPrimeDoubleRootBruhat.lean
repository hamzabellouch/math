import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootTranslation

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    p^2*((1-9*x*y)/p^2)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeDoubleRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p^2,3*x;-3*y,(1-9*x*y)/p^2],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeDoubleRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeDoubleRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaPrimeDoubleRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (p^2) ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p^2)
  refine ⟨(cubicThetaPrimeDouble_primary hp),⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p^2-1
  apply (primary_coprime_three (cubicThetaPrimeDouble_primary hp)).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeDoubleRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr (cubicThetaPrimeDouble_primary hp)) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  ring

def cubicThetaPrimeDoubleRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeDoubleRootBruhatMatrix hp x y hxy,cubicThetaPrimeDoubleRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeDoubleRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootBruhat hp x y hxy)=cubicSymbol (p^2) (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (p^2) (-3*y)=cubicSymbol (p^2) (3*y)
  rw [neg_mul,cubicSymbol_neg (cubicThetaPrimeDouble_primary hp)]


theorem cubicThetaPrimeDoubleRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaPrimeDoubleRootElement hp y*cubicThetaPrimeDoubleRootWeylElement hp*cubicThetaPrimeDoubleRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootBruhat hp x y hxy) := by
  have hpC : ((p^2:Eisenstein):ℂ)≠0 := fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)
  have hp1C : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p^2:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/((p^2:Eisenstein):ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = ((p^2:Eisenstein):ℂ)*(((1-9*x*y)/p^2:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeDoubleRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeDoubleRootElement_translation,cubicThetaPrimeDoubleRootElement_translation,
    cubicThetaPrimeDoubleRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix ((p^2:Eisenstein):ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeDoubleRootBruhat,cubicThetaPrimeDoubleRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp [hp1C]
  all_goals try rw [hthree]
  all_goals ring

theorem cubicThetaPrimeDoubleRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeDoubleRootElement hp y •
      (cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrimeDoubleRootElement hp x • z)))=
      cubicSymbol (p^2) (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeDoubleRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeDoubleRootBruhat_kubota]


end CubicFirstMoment

end

end OAI
