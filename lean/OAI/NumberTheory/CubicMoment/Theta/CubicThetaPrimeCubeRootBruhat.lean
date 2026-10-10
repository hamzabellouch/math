import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTranslation

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    p^3*((1-9*x*y)/p^3)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeCubeRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p^3,3*x;-3*y,(1-9*x*y)/p^3],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeCubeRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeCubeRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaPrimeCubeRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (p^3) ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p^3)
  refine ⟨(cubicThetaPrimeCube_primary hp),⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p^3-1
  apply (primary_coprime_three (cubicThetaPrimeCube_primary hp)).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeCubeRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr (cubicThetaPrimeCube_primary hp)) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  ring

def cubicThetaPrimeCubeRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeCubeRootBruhatMatrix hp x y hxy,cubicThetaPrimeCubeRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeCubeRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootBruhat hp x y hxy)=cubicSymbol (p^3) (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (p^3) (-3*y)=cubicSymbol (p^3) (3*y)
  rw [neg_mul,cubicSymbol_neg (cubicThetaPrimeCube_primary hp)]


theorem cubicThetaPrimeCubeRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaPrimeCubeRootElement hp y*cubicThetaPrimeCubeRootWeylElement hp*cubicThetaPrimeCubeRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootBruhat hp x y hxy) := by
  have hpC : ((p^3:Eisenstein):ℂ)≠0 := fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he)
  have hp1C : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p^3:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/((p^3:Eisenstein):ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = ((p^3:Eisenstein):ℂ)*(((1-9*x*y)/p^3:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeCubeRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeCubeRootElement_translation,
    cubicThetaPrimeCubeRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix ((p^3:Eisenstein):ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeRootBruhat,cubicThetaPrimeCubeRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp [hp1C]
  all_goals try rw [hthree]
  all_goals ring

theorem cubicThetaPrimeCubeRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeRootElement hp y •
      (cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootElement hp x • z)))=
      cubicSymbol (p^3) (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeCubeRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeCubeRootBruhat_kubota]


end CubicFirstMoment

end

end OAI
