import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedSeries

namespace OAI

/-! The integral Bruhat calculation for the primary levels occurring
in the Voronoi formula. The multiplier is computed from the actual matrix. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaLevelBruhat_division {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) :
    q*((1-9*x*y)/q)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' (primary_ne_zero hq)
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaLevelBruhatMatrix {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![q,3*x;-3*y,(1-9*x*y)/q],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaLevelBruhat_division hq x y hxy⟩

lemma cubicThetaLevelBruhatMatrix_mem {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) :
    cubicThetaLevelBruhatMatrix hq x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary q ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/q)
  refine ⟨hq,⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/q-1
  apply (primary_coprime_three hq).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaLevelBruhat_division hq x y hxy]
  convert dvd_sub (dvd_neg.mpr hq) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  ring

def cubicThetaLevelBruhat {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaLevelBruhatMatrix hq x y hxy,cubicThetaLevelBruhatMatrix_mem hq x y hxy⟩

lemma cubicThetaLevelBruhat_kubota {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaLevelBruhat hq x y hxy)=cubicSymbol q (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol q (-3*y)=cubicSymbol q (3*y)
  rw [neg_mul,cubicSymbol_neg hq]

theorem cubicThetaLevelBruhat_identity {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) :
    cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ))*
      cubicThetaInversionMatrix (q:ℂ) (fun he => primary_ne_zero hq (Subtype.ext he))*
        cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ))=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaLevelBruhat hq x y hxy) := by
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hd : (((1-9*x*y)/q:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/(q:ℂ) := by
    apply (eq_div_iff hqC).mpr
    calc
      _ = (q:ℂ)*(((1-9*x*y)/q:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaLevelBruhat_division hq x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (3*(y:ℂ)/(q:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix (q:ℂ) hqC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (3*(x:ℂ)/(q:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaLevelBruhat hq x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaLevelBruhat,cubicThetaLevelBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [show ((3:Eisenstein):ℂ)=3 from rfl]

end CubicFirstMoment

end

end OAI
