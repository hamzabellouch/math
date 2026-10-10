import Mathlib
import OAI.Analysis.Commutator.StinespringAction

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

open UniformSpace

namespace Kadison.Stinespring

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] lemma middleForm_add (φ : A →CP (H →L[ℂ] H)) (a b : A) (x y : PreSpace φ) :
    middleForm φ (a+b) x y=middleForm φ a x y+middleForm φ b x y := by
  classical
  simp [middleForm,Finsupp.sum,mul_add,add_mul,Finset.sum_add_distrib]

@[simp] lemma middleForm_smul (φ : A →CP (H →L[ℂ] H)) (c : ℂ) (a : A) (x y : PreSpace φ) :
    middleForm φ (c • a) x y=c*middleForm φ a x y := by
  classical
  simp [middleForm,Finsupp.sum,Finset.mul_sum]

@[simp] lemma middleForm_zero (φ : A →CP (H →L[ℂ] H)) (x y : PreSpace φ) :
    middleForm φ 0 x y=0 := by simp [middleForm,Finsupp.sum]

lemma leftLinear_one (φ : A →CP (H →L[ℂ] H)) : leftLinear φ 1=LinearMap.id := by
  ext x
  apply (ofPre φ).injective
  simp [leftLinear,Finsupp.lmapDomain_apply]

lemma leftLinear_mul (φ : A →CP (H →L[ℂ] H)) (a b : A) :
    leftLinear φ (a*b)=(leftLinear φ a).comp (leftLinear φ b) := by
  ext x
  apply (ofPre φ).injective
  simp only [leftLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,ofPre_toPre,Finsupp.lmapDomain_apply]
  rw [←Finsupp.mapDomain_comp]
  congr 1
  ext z
  simp [mul_assoc]

lemma coe_leftLinear_add (φ : A →CP (H →L[ℂ] H)) (a b : A) (x : PreSpace φ) :
    (leftLinear φ (a+b) x : Space φ)=(leftLinear φ a x : Space φ)+(leftLinear φ b x : Space φ) := by
  apply ext_inner_right ℂ
  intro y
  induction y using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih y =>
    rw [←Completion.coe_add,Completion.inner_coe,Completion.inner_coe]
    simp [inner_def,form_add_left,form_left,star_add]

lemma coe_leftLinear_smul (φ : A →CP (H →L[ℂ] H)) (c : ℂ) (a : A) (x : PreSpace φ) :
    (leftLinear φ (c • a) x : Space φ)=c • (leftLinear φ a x : Space φ) := by
  apply ext_inner_right ℂ
  intro y
  induction y using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih y =>
    rw [←Completion.coe_smul,Completion.inner_coe,Completion.inner_coe]
    simp [inner_def,form_smul_left,form_left,star_smul]

lemma coe_leftLinear_zero (φ : A →CP (H →L[ℂ] H)) (x : PreSpace φ) :
    (leftLinear φ 0 x : Space φ)=0 := by
  simpa using coe_leftLinear_smul φ 0 0 x

def representation (φ : A →CP (H →L[ℂ] H)) : A →⋆ₐ[ℂ] (Space φ →L[ℂ] Space φ) where
  toFun a := (leftAction φ a).completion
  map_one' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [leftLinear_one]
  map_mul' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [leftLinear_mul,LinearMap.comp_apply]
  map_zero' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [coe_leftLinear_zero]
  map_add' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [coe_leftLinear_add]
  commutes' c := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [Algebra.algebraMap_eq_smul_one,coe_leftLinear_smul,leftLinear_one]
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    induction x,y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simp [inner_def,form_left,form_right]

@[simp] lemma representation_coe (φ : A →CP (H →L[ℂ] H)) (a : A) (x : PreSpace φ) :
    representation φ a (x : Space φ)=(leftLinear φ a x : Space φ) := by
  change (leftAction φ a).completion (x : Space φ)=_
  simp

end Kadison.Stinespring

end

end
end

end OAI
