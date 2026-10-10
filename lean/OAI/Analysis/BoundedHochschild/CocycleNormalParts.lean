import Mathlib
import OAI.Analysis.BoundedHochschild.BarDifferential
import OAI.Analysis.BoundedHochschild.NormalOperators

namespace OAI

/-! Normal corrections and first- and last-input normal cocycles. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 
def normalLast {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  ((operatorNormalPart e).compContinuousMultilinearMap f.curryRight).uncurryRight

@[simp] lemma normalLast_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin (n+1) → M) :
    normalLast e f v=operatorNormalPart e (f.curryRight (fun i => v i.castSucc)) (v (Fin.last n)) := rfl

@[simp] lemma normalLast_snoc {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) (a : M) :
    normalLast e f (Fin.snoc v a)=operatorNormalPart e (f.curryRight v) a := by
  simp

lemma normalLast_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e ((normalLast e f).curryRight v) := by
  have h : (normalLast e f).curryRight v=operatorNormalPart e (f.curryRight v) := by
    ext a
    simp only [ContinuousMultilinearMap.curryRight_apply,normalLast_snoc]
  rw [h]
  exact operatorNormalPart_normal e (f.curryRight v)

 

lemma normalLast_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+1) → M) (a : M) :
    v 0*normalLast e f (Fin.snoc (fun i : Fin n => v i.succ) a)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • normalLast e f (Fin.snoc (mergeInputs v j) a))+
      ((-1:ℂ)^(n+1)) • normalLast e f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*a))+
      ((-1:ℂ)^(n+2)) • (f v*a)=0 := by
  let L := ContinuousLinearMap.mul ℂ M
  have h : (L (v 0)).comp (f.curryRight (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • f.curryRight (mergeInputs v j))+
      ((-1:ℂ)^(n+1)) • (f.curryRight (fun i : Fin n => v i.castSucc)).comp (L (v (Fin.last n)))+
      ((-1:ℂ)^(n+2)) • L (f v)=0 := by
    ext b
    have h := hf (Fin.snoc v b)
    rw [differentialValue_snoc] at h
    simpa only [L,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply',ContinuousMultilinearMap.curryRight_apply,zero_apply] using h
  have h' := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T a) h
  dsimp only [L] at h'
  simp only [map_add,map_sum,map_smul,map_zero,zero_apply,
    operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).1 (v 0)),
    operatorNormalPart_comp_left,
    operatorNormalPart_fixes e _ ((HochschildSakai.abstract_multiplication_normal e).1 (f v)),
    add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply] at h'
  simpa only [normalLast_snoc,ContinuousLinearMap.mul_apply'] using h'

 
def reducedNormalCocycle {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  normalLast e f-rightCoboundary (insertLast (normalLast e f) 1)

def normalCorrection {n : ℕ} (f : Cochain M (n+1)) : Cochain M n :=
  ((-1:ℂ)^(n+1)) • insertLast (normalLast e f) 1

lemma sign_square (k : ℕ) : (-1:ℂ)^k*(-1:ℂ)^k=1 := by
  rw [← mul_pow]
  simp

lemma sign_succ (k : ℕ) : (-1:ℂ)^(k+1) = -((-1:ℂ)^k) := by
  rw [pow_succ]
  ring

lemma normal_correction_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+1) → M) :
    f v=reducedNormalCocycle e f v+differentialValue (normalCorrection e f) v := by
  let F := normalLast e f
  let h := insertLast F 1
  let s := (-1:ℂ)^(n+1)
  have he := normalLast_identity e f hf v 1
  have hs : (-1:ℂ)^(n+2) = -s := sign_succ (n+1)
  have hv : Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n))=v := Fin.snoc_init_self v
  simp only [mul_one,hv,hs] at he
  have hA : differentialValue h v+s • (F v-rightCoboundary h v)-s • f v=0 := by
    change v 0*F (Fin.snoc (fun i : Fin n => v i.succ) 1)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • F (Fin.snoc (mergeInputs v j) 1))+
      s • F v+(-s) • f v=0 at he
    dsimp only [h]
    simp only [differentialValue,insertLast_apply,rightCoboundary_apply,smul_sub,neg_smul] at *
    linear_combination (norm := module) he
  have hB : differentialValue h v+s • (F v-rightCoboundary h v)=s • f v := sub_eq_zero.mp hA
  have hC := congrArg (fun b : M => s • b) hB
  simp only [smul_add,smul_smul,show s*s=1 from sign_square (n+1),one_smul] at hC
  rw [normalCorrection,differentialValue_smul]
  change f v=(F v-rightCoboundary h v)+s • differentialValue h v
  exact hC.symm.trans (add_comm _ _)

lemma reducedNormalCocycle_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e ((reducedNormalCocycle e f).curryRight v) := by
  intro z
  obtain ⟨z₁,hz₁⟩ := normalLast_normal e f v z
  obtain ⟨z₂,hz₂⟩ := (HochschildSakai.abstract_multiplication_normal e).1
    (insertLast (normalLast e f) 1 v) z
  refine ⟨z₁-z₂,?_⟩
  intro a
  simp only [reducedNormalCocycle,ContinuousMultilinearMap.curryRight_apply,
    sub_apply,rightCoboundary_apply,Fin.snoc_castSucc,Fin.snoc_last]
  change e.symm (normalLast e f (Fin.snoc v a) - insertLast (normalLast e f) 1 v*a) z =
    e.symm a (z₁-z₂)
  rw [map_sub,sub_apply,map_sub]
  exact congrArg₂ (·-·) (hz₁ a) (hz₂ a)

lemma differentialValue_sub {n : ℕ} (f g : Cochain M n) (v : Fin (n+1) → M) :
    differentialValue (f-g) v=differentialValue f v-differentialValue g v := by
  rw [sub_eq_add_neg,show -g=(-1:ℂ) • g by simp,differentialValue_add,differentialValue_smul]
  simp [sub_eq_add_neg]

lemma rightCoboundary_differential {n : ℕ} (h : Cochain M n)
    (v : Fin (n+1) → M) (a : M) :
    differentialValue (rightCoboundary h) (Fin.snoc v a)=
      (differentialValue h v-((-1:ℂ)^(n+1)) • rightCoboundary h v)*a := by
  rw [differentialValue_snoc,sign_succ (n+1)]
  simp only [rightCoboundary_apply,Fin.snoc_castSucc,Fin.snoc_last,differentialValue,
    add_mul,sub_mul,Finset.sum_mul,smul_mul_assoc,mul_assoc,neg_smul]
  abel

lemma reducedNormalCocycle_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (x : Fin (n+2) → M) :
    differentialValue (reducedNormalCocycle e f) x=0 := by
  let v : Fin (n+1) → M := fun i => x i.castSucc
  let a := x (Fin.last (n+1))
  have hx : x=Fin.snoc v a := (Fin.snoc_init_self x).symm
  rw [hx,reducedNormalCocycle,differentialValue_sub,rightCoboundary_differential,differentialValue_snoc]
  have h := normalLast_identity e f hf v a
  have hv := normal_correction_identity e f hf v
  rw [reducedNormalCocycle,sub_apply,normalCorrection,differentialValue_smul] at hv
  have hs : (-1:ℂ)^(n+2) = -((-1:ℂ)^(n+1)) := sign_succ (n+1)
  rw [hs] at h ⊢
  rw [hv] at h
  simp only [add_mul,sub_mul,smul_mul_assoc,smul_add,smul_sub,neg_smul,smul_smul,
    neg_mul,sign_square,one_smul] at h ⊢
  linear_combination (norm := module) h

lemma normalLast_norm {n : ℕ} (f : Cochain M (n+1)) : ‖normalLast e f‖≤4*‖f‖ := by
  have hN : ‖operatorNormalPart e‖≤4 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (normalOperator_norm e)
  rw [normalLast,ContinuousMultilinearMap.uncurryRight_norm]
  calc
    _ ≤ ‖operatorNormalPart e‖*‖f.curryRight‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 4*‖f‖ := by rw [ContinuousMultilinearMap.curryRight_norm]; gcongr

lemma rightCoboundary_norm {n : ℕ} (f : Cochain M n) : ‖rightCoboundary f‖≤‖f‖ := by
  rw [rightCoboundary,ContinuousMultilinearMap.uncurryRight_norm]
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ M‖*‖f‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ M) (norm_nonneg _)
    _ = _ := one_mul _

lemma insertLast_one_norm {n : ℕ} (f : Cochain M (n+1)) : ‖insertLast f 1‖≤‖f‖ := by
  have h : ‖(1:M)‖≤1 := by
    rcases subsingleton_or_nontrivial M with h|h
    · simp [Subsingleton.elim (1:M) 0]
    · simp
  exact (norm_insertLast_le f 1).trans ((mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (mul_one _))

lemma reducedNormalCocycle_norm {n : ℕ} (f : Cochain M (n+1)) :
    ‖reducedNormalCocycle e f‖≤8*‖f‖ := by
  have h := (rightCoboundary_norm (insertLast (normalLast e f) 1)).trans (insertLast_one_norm _)
  have hN := normalLast_norm e f
  exact (norm_sub_le _ _).trans (by linarith)

lemma normalCorrection_norm {n : ℕ} (f : Cochain M (n+1)) : ‖normalCorrection e f‖≤4*‖f‖ := by
  simpa only [normalCorrection,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    using (insertLast_one_norm (normalLast e f)).trans (normalLast_norm e f)

 

theorem ordinary_to_last_normal {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) :
    ∃ F : Cochain M (n+1), ∃ h : Cochain M n,
      (∀ v,differentialValue F v=0) ∧
      (∀ v : Fin n → M,HasPreadjoint e (F.curryRight v)) ∧
      ∀ v,f v=F v+differentialValue h v :=
  ⟨reducedNormalCocycle e f,normalCorrection e f,reducedNormalCocycle_cocycle e f hf,
    reducedNormalCocycle_normal e f,normal_correction_identity e f hf⟩

end BoundedHochschild

 

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def reverseArguments {n : ℕ} (f : Cochain M n) : Cochain M n :=
  ContinuousMultilinearMap.domDomCongr Fin.revPerm f

lemma reverseArguments_apply {n : ℕ} (f : Cochain M n) (v : Fin n → M) :
    reverseArguments f v=f (v ∘ Fin.rev) := rfl

@[simp] lemma reverseArguments_norm {n : ℕ} (f : Cochain M n) : ‖reverseArguments f‖=‖f‖ :=
  ContinuousMultilinearMap.norm_domDomCongr ℂ M M _ _

def firstSliceN {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) : M →L[ℂ] M :=
  (reverseArguments f).curryRight (v ∘ Fin.rev)

@[simp] lemma firstSliceN_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) (a : M) :
    firstSliceN f v a=f (Fin.cons a v) := by
  change reverseArguments f (Fin.snoc (v ∘ Fin.rev) a)=_
  rw [reverseArguments_apply,Fin.snoc_comp_rev]
  have hv : (v ∘ Fin.rev) ∘ Fin.rev=v := by
    ext i
    simp
  rw [hv]

 
def normalFirst {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  reverseArguments (normalLast e (reverseArguments f))

@[simp] lemma normalFirst_cons {n : ℕ} (f : Cochain M (n+1)) (a : M) (v : Fin n → M) :
    normalFirst e f (Fin.cons a v)=operatorNormalPart e (firstSliceN f v) a := by
  rw [normalFirst,reverseArguments_apply,Fin.cons_comp_rev,normalLast_snoc]
  rfl

lemma normalFirst_norm {n : ℕ} (f : Cochain M (n+1)) : ‖normalFirst e f‖≤4*‖f‖ := by
  simpa only [normalFirst,reverseArguments_norm] using normalLast_norm e (reverseArguments f)

lemma normalFirst_normal {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    HasPreadjoint e (firstSliceN (normalFirst e f) v) := by
  have he : firstSliceN (normalFirst e f) v=operatorNormalPart e (firstSliceN f v) := by
    ext a
    simp
  rw [he]
  exact operatorNormalPart_normal e _

lemma differentialValue_cons {n : ℕ} (f : Cochain M (n+1))
    (a : M) (v : Fin (n+1) → M) :
    differentialValue f (Fin.cons a v)=a*f v-f (Fin.cons (a*v 0) (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • f (Fin.cons a (mergeInputs v j)))+
      ((-1:ℂ)^(n+2)) • (f (Fin.cons a (fun i : Fin n => v i.castSucc))*v (Fin.last n)) := by
  have hinit : (fun i : Fin (n+1) => (Fin.cons a v : Fin (n+2) → M) i.castSucc)=
      Fin.cons a (fun i : Fin n => v i.castSucc) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.castSucc_succ,Fin.cons_succ]
  have hlast : (Fin.cons a v : Fin (n+2) → M) (Fin.last (n+1))=v (Fin.last n) := by
    change (Fin.cons a v : Fin (n+2) → M) (Fin.last n).succ=_
    simp
  simp only [differentialValue,Fin.cons_zero,Fin.cons_succ,hinit,hlast,
    Fin.sum_univ_succ,mergeInputs_cons_zero,mergeInputs_cons_succ,
    Fin.val_zero,zero_add,pow_one,neg_smul,one_smul,Fin.val_succ,Nat.add_assoc]
  abel

lemma normalFirst_identity {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (a : M) (v : Fin (n+1) → M) :
    a*f v-normalFirst e f (Fin.cons (a*v 0) (fun i : Fin n => v i.succ))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • normalFirst e f (Fin.cons a (mergeInputs v j)))+
      ((-1:ℂ)^(n+2)) • (normalFirst e f (Fin.cons a (fun i : Fin n => v i.castSucc))*v (Fin.last n))=0 := by
  let R := (ContinuousLinearMap.mul ℂ M).flip
  have hop : R (f v)-(firstSliceN f (fun i : Fin n => v i.succ)).comp (R (v 0))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+2)) • firstSliceN f (mergeInputs v j))+
      ((-1:ℂ)^(n+2)) • (R (v (Fin.last n))).comp (firstSliceN f (fun i : Fin n => v i.castSucc))=0 := by
    ext b
    simpa only [R,sub_apply,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',firstSliceN_apply,zero_apply,
      differentialValue_cons] using hf (Fin.cons b v)
  have h := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T a) hop
  dsimp only [R] at h
  simp only [map_sub,map_add,map_sum,map_smul,map_zero,sub_apply,add_apply,sum_apply,smul_apply,zero_apply,
    operatorNormalPart_fixes e _ ((HochschildSakai.abstract_multiplication_normal e).2 _),
    operatorNormalPart_comp_right,operatorNormalPart_comp_normal e _ _
      ((HochschildSakai.abstract_multiplication_normal e).2 _),
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',← normalFirst_cons] at h
  exact h

 
def firstNormalCorrectionN {n : ℕ} (f : Cochain M (n+1)) : Cochain M n :=
  (normalFirst e f).curryLeft 1

def firstNormalRemainderN {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  f-differential (firstNormalCorrectionN e f)

@[simp] lemma firstNormalCorrectionN_apply {n : ℕ} (f : Cochain M (n+1)) (v : Fin n → M) :
    firstNormalCorrectionN e f v=normalFirst e f (Fin.cons 1 v) := rfl

lemma firstNormalRemainderN_apply {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (v : Fin (n+1) → M) :
    firstNormalRemainderN e f v=normalFirst e f v-
      v 0*normalFirst e f (Fin.cons 1 (fun i : Fin n => v i.succ)) := by
  have h := normalFirst_identity e f hf 1 v
  have hv : Fin.cons (v 0) (fun i : Fin n => v i.succ)=v := Fin.cons_self_tail v
  simp only [one_mul,hv] at h
  simp only [firstNormalRemainderN,sub_apply,differential_apply,differentialValue,
    firstNormalCorrectionN_apply]
  have hsign (j : Fin n) : (-1:ℂ)^(j.val+2) = -((-1:ℂ)^(j.val+1)) := sign_succ _
  rw [sign_succ (n+1)] at h
  simp only [hsign,neg_smul,Finset.sum_neg_distrib] at h
  linear_combination (norm := module) h

lemma firstNormalRemainderN_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ z,differentialValue f z=0) (z : Fin (n+2) → M) :
    differentialValue (firstNormalRemainderN e f) z=0 := by
  rw [firstNormalRemainderN,differentialValue_sub,hf,differential_is_cocycle,sub_self]

lemma firstNormalRemainderN_identity {n : ℕ} (f : Cochain M (n+1)) (v : Fin (n+1) → M) :
    f v=firstNormalRemainderN e f v+differentialValue (firstNormalCorrectionN e f) v := by
  simp only [firstNormalRemainderN,sub_apply,differential_apply,sub_add_cancel]

lemma firstNormalCorrectionN_norm {n : ℕ} (f : Cochain M (n+1)) :
    ‖firstNormalCorrectionN e f‖≤4*‖f‖ := by
  have h1 : ‖(1:M)‖≤1 := by
    rcases subsingleton_or_nontrivial M with h|h
    · simp [Subsingleton.elim (1:M) 0]
    · simp
  calc
    _≤‖(normalFirst e f).curryLeft‖*‖(1:M)‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖normalFirst e f‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]; nlinarith [norm_nonneg (normalFirst e f)]
    _≤_ := normalFirst_norm e f

end BoundedHochschild
end

end OAI
