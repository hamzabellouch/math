import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.HilbertNormalParts
import OAI.Analysis.TracialCohomology.InteriorHomotopy

namespace OAI

/-! Slot homotopy for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def sliceAt {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) : M →L[ℂ] M := (f.curryMid i).flipMultilinear v

@[simp] lemma sliceAt_apply {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) (a : M) : sliceAt f i v a=f (i.insertNth a v) := rfl

def normalAt {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) : Cochain M (n+1) :=
  (((operatorNormalPart e).compContinuousMultilinearMap
    (f.curryMid i).flipMultilinear).flipLinear).uncurryMid i

@[simp] lemma normalAt_insert {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) (a : M) :
    normalAt e f i (i.insertNth a v)=operatorNormalPart e (sliceAt f i v) a := by
  change (((normalAt e f i).curryMid i) a) v=_
  rw [normalAt,ContinuousLinearMap.curryMid_uncurryMid]
  rfl

lemma normalAt_normal {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) : HasPreadjoint e (sliceAt (normalAt e f i) i v) := by
  have heq : sliceAt (normalAt e f i) i v=operatorNormalPart e (sliceAt f i v) := by
    ext a
    exact normalAt_insert e f i v a
  rw [heq]
  exact operatorNormalPart_normal e _

def slotInsertion {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) : Cochain M n :=
  (normalAt e f i).curryMid i 1

@[simp] lemma slotInsertion_apply {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) :
    slotInsertion e f i v=operatorNormalPart e (sliceAt f i v) 1 := normalAt_insert e f i v 1

lemma sliceAt_norm {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) (v : Fin n → M) :
    ‖sliceAt f i v‖≤‖f‖*∏ j,‖v j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [sliceAt_apply]
  calc
    _ ≤ ‖f‖*‖a‖*∏ j,‖v j‖ := f.norm_map_insertNth_le a v
    _ = _ := by ring

lemma normalAt_norm {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) :
    ‖normalAt e f i‖≤4*‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [← Fin.insertNth_self_removeNth i v,normalAt_insert]
  calc
    _ ≤ ‖operatorNormalPart e (sliceAt f i (i.removeNth v))‖*‖v i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4*‖sliceAt f i (i.removeNth v)‖)*‖v i‖ := by
      gcongr
      exact normalOperator_norm e _
    _ ≤ (4*(‖f‖*∏ j,‖i.removeNth v j‖))*‖v i‖ := by
      gcongr
      exact sliceAt_norm f i _
    _ = 4*‖f‖*∏ j,‖(i.insertNth (v i) (i.removeNth v)) j‖ := by
      rw [Fin.prod_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
      ring

lemma slotInsertion_norm {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1)) :
    ‖slotInsertion e f i‖≤4*‖f‖ := by
  have h1 : ‖(1:M)‖≤1 := by
    rcases subsingleton_or_nontrivial M with h|h
    · simp [Subsingleton.elim (1:M) 0]
    · simp
  calc
    _ ≤ ‖(normalAt e f i).curryMid i‖*‖(1:M)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4*‖f‖)*1 := by
      rw [ContinuousMultilinearMap.norm_curryMid]
      gcongr
      exact normalAt_norm e f i
    _ = _ := mul_one _

lemma merge_insert_product {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (a : M) :
    mergeInputs (r.castSucc.insertNth a v) r=Function.update v r (a*v r) := by
  ext i
  by_cases hir : i < r
  · simp only [mergeInputs,ite_eq_left hir,Function.update_of_ne (ne_of_lt hir)]
    rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.lt_def] using hir)]
    rfl
  · by_cases he : i=r
    · subst i
      simp only [mergeInputs,lt_self_iff_false,ite_false,ite_true,Function.update_self,
        Fin.insertNth_apply_same]
      rw [tupleInsert_gt _ _ _ _ (by simp)]
      rfl
    · simp only [mergeInputs,ite_eq_right hir,ite_eq_right he,Function.update_of_ne he]
      rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_succ]; omega)]
      rfl

lemma merge_insert_prev {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1=r.val) (a : M) :
    mergeInputs (r.castSucc.insertNth a v) (r.succAbove j)=
      Function.update v j.castSucc (v j.castSucc*a) := by
  have hs : r.succAbove j=j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
  rw [hs]
  ext i
  by_cases hij : i<j.castSucc
  · simp only [mergeInputs,ite_eq_left hij,Function.update_of_ne (ne_of_lt hij)]
    exact tupleInsert_lt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.lt_def] at *; omega)
  · by_cases he : i=j.castSucc
    · subst i
      simp only [mergeInputs,lt_self_iff_false,ite_false,ite_true,Function.update_self]
      rw [tupleInsert_lt _ _ _ _ (by simp only [Fin.val_castSucc]; omega)]
      have hi : j.castSucc.succ=r.castSucc := Fin.ext hjr
      rw [hi,Fin.insertNth_apply_same]
      rfl
    · simp only [mergeInputs,ite_eq_right hij,ite_eq_right he,Function.update_of_ne he]
      rw [tupleInsert_gt _ _ _ _ (by
        simp only [Fin.val_castSucc,Fin.val_succ,Fin.lt_def,Fin.ext_iff] at *
        omega)]
      rfl

lemma sliceAt_add {n : ℕ} (f g : Cochain M (n+1)) (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (f+g) i v=sliceAt f i v+sliceAt g i v := by ext a; simp

lemma sliceAt_smul {n : ℕ} (c : ℂ) (f : Cochain M (n+1)) (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (c • f) i v=c • sliceAt f i v := by ext a; simp

lemma sliceAt_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cochain M (n+1))
    (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (∑ j ∈ s,f j) i v=∑ j ∈ s,sliceAt (f j) i v := by ext a; simp

lemma sliceAt_zero {n : ℕ} (i : Fin (n+1)) (v : Fin n → M) :
    sliceAt (0 : Cochain M (n+1)) i v=0 := by ext a; simp

lemma sliceAt_left {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) (hr : 0<r.val)
    (v : Fin (n+1) → M) :
    sliceAt (leftCoboundary f) r.castSucc v=
      (ContinuousLinearMap.mul ℂ M (v 0)).comp
        (sliceAt f ⟨r.val-1,by omega⟩ (fun i => v i.succ)) := by
  ext a
  simp only [sliceAt_apply,leftCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [tupleInsert_lt _ _ _ _ hr,tail_insert v r a hr]
  rfl

lemma sliceAt_right {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    sliceAt (rightCoboundary f) r.castSucc v=
      ((ContinuousLinearMap.mul ℂ M).flip (v (Fin.last n))).comp
        (sliceAt f r (fun i => v i.castSucc)) := by
  ext a
  simp only [sliceAt_apply,rightCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
  rw [init_insert,last_insert]

lemma sliceAt_middle_same {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f r) r.castSucc v=
      (sliceAt f r (r.removeNth v)).comp ((ContinuousLinearMap.mul ℂ M).flip (v r)) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',merge_insert_product,
    Fin.insertNth_removeNth]

lemma sliceAt_middle_before {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1<r.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      sliceAt f ⟨r.val-1,by omega⟩ (mergeInputs v j) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,merge_insert_before v r _ j hjr]

lemma sliceAt_middle_after {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : r.val≤j.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      sliceAt f r (mergeInputs v j) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,merge_insert_after v r _ j hjr]

lemma sliceAt_middle_before_boundary {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : j.val+1=r.val) (v : Fin (n+1) → M) :
    sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v=
      (sliceAt f j.castSucc (j.castSucc.removeNth v)).comp
        (ContinuousLinearMap.mul ℂ M (v j.castSucc)) := by
  ext a
  simp only [sliceAt_apply,middleCoboundary_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply',merge_insert_prev v r j hjr,Fin.insertNth_removeNth]

def NormalBefore {n : ℕ} (f : Cochain M (n+1)) (r : ℕ) : Prop :=
  ∀ i : Fin (n+1), i.val<r → ∀ v,HasPreadjoint e (sliceAt f i v)

def UnitZeroBefore {n : ℕ} (f : Cochain M (n+1)) (r : ℕ) : Prop :=
  ∀ i : Fin (n+1), i.val<r → ∀ v,f (i.insertNth 1 v)=0

lemma projected_left_zero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (leftCoboundary f) r.castSucc v) 1=0 := by
  rw [sliceAt_left f r hr v,operatorNormalPart_comp_normal e _ _
    ((HochschildSakai.abstract_multiplication_normal e).1 _),
    operatorNormalPart_fixes e _ (hN _ (by dsimp; omega) _)]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',sliceAt_apply]
  rw [hU _ (by dsimp; omega),mul_zero]

lemma projected_middle_before_zero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (j : Fin n) (hjr : j.val+1<r.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=0 := by
  rw [sliceAt_middle_before f r j hjr v,
    operatorNormalPart_fixes e _ (hN _ (by dsimp; omega) _),sliceAt_apply]
  exact hU _ (by dsimp; omega) _

lemma projected_middle_boundary {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hN : NormalBefore e f r.val)
    (j : Fin n) (hjr : j.val+1=r.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=f v := by
  rw [sliceAt_middle_before_boundary f r j hjr v,operatorNormalPart_fixes e _
    ((hN j.castSucc (by simp only [Fin.val_castSucc]; omega) _).comp e
      ((HochschildSakai.abstract_multiplication_normal e).1 _))]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',mul_one,
    sliceAt_apply,Fin.insertNth_self_removeNth]

lemma projected_middle_same {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f r) r.castSucc v) 1=normalAt e f r v := by
  rw [sliceAt_middle_same,operatorNormalPart_comp_right]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',one_mul]
  rw [← normalAt_insert,Fin.insertNth_self_removeNth]

lemma projected_middle_after {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (j : Fin n) (hjr : r.val≤j.val) (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=
      slotInsertion e f r (mergeInputs v j) := by
  rw [sliceAt_middle_after f r j hjr v,slotInsertion_apply]

lemma projected_right {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    operatorNormalPart e (sliceAt (rightCoboundary f) r.castSucc v) 1=
      slotInsertion e f r (fun i => v i.castSucc)*v (Fin.last n) := by
  rw [sliceAt_right,operatorNormalPart_comp_normal e _ _
    ((HochschildSakai.abstract_multiplication_normal e).2 _)]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',slotInsertion_apply]

lemma projected_middle_sum {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    (∑ j : Fin (n+1),((-1:ℂ)^(j.val+1)) •
      operatorNormalPart e (sliceAt (middleCoboundary f j) r.castSucc v) 1)=
    ((-1:ℂ)^(r.val+1)) • normalAt e f r v + ((-1:ℂ)^r.val) • f v +
      ∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0 := by
  rw [Fin.sum_univ_succAbove _ r,projected_middle_same]
  let b : Fin n := ⟨r.val-1,by omega⟩
  have hj (j : Fin n) :
      ((-1:ℂ)^((r.succAbove j).val+1)) •
        operatorNormalPart e (sliceAt (middleCoboundary f (r.succAbove j)) r.castSucc v) 1=
      (if j=b then ((-1:ℂ)^r.val) • f v else 0) +
      (if r.val≤j.val then ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0) := by
    rcases lt_trichotomy (j.val+1) r.val with h|h|h
    · rw [projected_middle_before_zero e f r hN hU j h v]
      have hb : j≠b := by intro he; have := congrArg Fin.val he; dsimp [b] at this; omega
      simp only [hb,ite_false,show ¬r.val≤j.val by omega,smul_zero,add_zero]
    · have he : j=b := Fin.ext (by dsimp [b]; omega)
      have hs : r.succAbove j=j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
      rw [projected_middle_boundary e f r hN j h v,hs]
      simp only [Fin.val_castSucc]
      rw [h]
      simp only [he,ite_true,show ¬r.val≤b.val by dsimp [b]; omega,ite_false,add_zero]
    · have hle : r.val≤j.val := by omega
      have hb : j≠b := by intro he; have := congrArg Fin.val he; dsimp [b] at this; omega
      have hs : r.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [projected_middle_after e f r j hle v,hs]
      simp only [Fin.val_succ,hb,ite_false,hle,ite_true,zero_add]
  simp_rw [hj]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  abel

lemma slot_cocycle_identity {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    ((-1:ℂ)^r.val) • f v + ((-1:ℂ)^(r.val+1)) • normalAt e f r v +
      (∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0) +
      ((-1:ℂ)^(n+2)) •
        (slotInsertion e f r (fun i => v i.castSucc)*v (Fin.last n))=0 := by
  have hd : differential f=0 := by ext w; simpa only [differential_apply,zero_apply] using hf w
  have hp := congrArg (fun T : Cochain M (n+2) =>
    operatorNormalPart e (sliceAt T r.castSucc v) 1) hd
  simp only [differential,sliceAt_add,sliceAt_sum,sliceAt_smul,sliceAt_zero,
    map_add,map_sum,map_smul,map_zero,add_apply,sum_apply,smul_apply,zero_apply] at hp
  rw [projected_left_zero e f r hr hN hU v,projected_right,
    projected_middle_sum e f r hr hN hU v,zero_add] at hp
  convert hp using 1
  abel

def prefixDifferential : {n : ℕ} → Cochain M n → ℕ → Cochain M (n+1)
  | 0,h,_ => leftCoboundary h
  | n+1,h,r => leftCoboundary h + ∑ j : Fin (n+1),if j.val<r then
      ((-1:ℂ)^(j.val+1)) • middleCoboundary h j else 0

@[simp] lemma prefixDifferential_apply {n : ℕ} (h : Cochain M n) (r : ℕ)
    (v : Fin (n+1) → M) :
    prefixDifferential h r v=v 0*h (fun i => v i.succ) +
      ∑ j : Fin n,if j.val<r then ((-1:ℂ)^(j.val+1)) • h (mergeInputs v j) else 0 := by
  cases n with
  | zero => simp [prefixDifferential]
  | succ n =>
    simp only [prefixDifferential,add_apply,leftCoboundary_apply,sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [smul_apply,middleCoboundary_apply,zero_apply]

def slotRemainder {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) : Cochain M (n+1) :=
  f-((-1:ℂ)^r.val) • differential (slotInsertion e f r)

def slotCorrection {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) : Cochain M n :=
  ((-1:ℂ)^r.val) • slotInsertion e f r

lemma slotCorrection_norm {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1)) :
    ‖slotCorrection e f r‖≤4*‖f‖ := by
  simp only [slotCorrection,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  exact slotInsertion_norm e f r

lemma slotRemainder_identity {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (v : Fin (n+1) → M) :
    f v=slotRemainder e f r v+differentialValue (slotCorrection e f r) v := by
  simp only [slotRemainder,slotCorrection,sub_apply,smul_apply,differential_apply,
    differentialValue_smul,sub_add_cancel]

lemma slotRemainder_cocycle {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+2) → M) :
    differentialValue (slotRemainder e f r) v=0 := by
  rw [slotRemainder,sub_eq_add_neg,← neg_one_smul ℂ (((-1:ℂ)^r.val) •_),
    differentialValue_add,differentialValue_smul,differentialValue_smul,
    hf,differential_is_cocycle,smul_zero,smul_zero,add_zero]

lemma slotRemainder_apply {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (v : Fin (n+1) → M) :
    slotRemainder e f r v=normalAt e f r v-
      ((-1:ℂ)^r.val) • prefixDifferential (slotInsertion e f r) r.val v := by
  have h := slot_cocycle_identity e f r hr hf hN hU v
  have hm : (∑ j : Fin n,if r.val≤j.val then
        ((-1:ℂ)^(j.val+2)) • slotInsertion e f r (mergeInputs v j) else 0)=
      (∑ j : Fin n,if j.val<r.val then
        ((-1:ℂ)^(j.val+1)) • slotInsertion e f r (mergeInputs v j) else 0)-
      ∑ j : Fin n,((-1:ℂ)^(j.val+1)) • slotInsertion e f r (mergeInputs v j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<r.val
    · simp only [hj,ite_true,show ¬r.val≤j.val by omega,ite_false,sub_self]
    · simp only [hj,ite_false,show r.val≤j.val by omega,ite_true,zero_sub,
        sign_succ (j.val+1),neg_smul]
  rw [hm,sign_succ r.val,sign_succ (n+1),neg_smul,neg_smul] at h
  have h' : ((-1:ℂ)^r.val) • (f v-normalAt e f r v)=
      differentialValue (slotInsertion e f r) v-
        prefixDifferential (slotInsertion e f r) r.val v := by
    simp only [differentialValue,prefixDifferential_apply,smul_sub]
    linear_combination (norm := module) h
  have h'' := congrArg (fun x : M => ((-1:ℂ)^r.val) • x) h'
  rw [smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul] at h''
  simp only [smul_sub] at h''
  simp only [slotRemainder,sub_apply,smul_apply,differential_apply]
  linear_combination (norm := module) h''

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma UnitZeroBefore.apply {n : ℕ} {f : Cochain M (n+1)} {r : ℕ}
    (hU : UnitZeroBefore f r) (v : Fin (n+1) → M) (i : Fin (n+1))
    (hi : i.val<r) (hv : v i=1) : f v=0 := by
  rw [← Fin.insertNth_self_removeNth i v,hv]
  exact hU i hi _

lemma normalAt_preserves_unitZero {n : ℕ} (f : Cochain M (n+1)) (r : Fin (n+1))
    (hU : UnitZeroBefore f r.val) : UnitZeroBefore (normalAt e f r) r.val := by
  intro i hi w
  let v : Fin (n+1) → M := i.insertNth (1:M) w
  have hir : i≠r := by intro hh; have := congrArg Fin.val hh; omega
  have hs : sliceAt f r (r.removeNth v)=0 := by
    ext a
    simp only [sliceAt_apply,Fin.insertNth_removeNth,zero_apply]
    apply hU.apply _ i hi
    rw [Function.update_of_ne hir]
    exact Fin.insertNth_apply_same _ _ _
  change normalAt e f r v=0
  rw [← Fin.insertNth_self_removeNth r v,normalAt_insert,hs,map_zero,zero_apply]

lemma insertion_preserves_unitZero {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hU : UnitZeroBefore f r.val) : UnitZeroBefore (slotInsertion e f r) r.val := by
  have hN := normalAt_preserves_unitZero e f r hU
  intro i hi v
  change normalAt e f r (r.insertNth 1 (i.insertNth 1 v))=0
  apply hN.apply _ i.castSucc hi
  rw [tupleInsert_lt _ _ _ _ hi]
  exact Fin.insertNth_apply_same _ _ _

def pairSlice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) : M →L[ℂ] M →L[ℂ] M :=
  (((f.curryMid r).flipMultilinear).curryMid i).flipMultilinear v

@[simp] lemma pairSlice_apply {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) (a b : M) :
    pairSlice f r i v a b=f (r.insertNth b (i.insertNth a v)) := rfl

lemma pairSlice_flip {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) (b : M) :
    (pairSlice f r i v).flip b=
      sliceAt f (r.succAbove i) ((r.succAbove i).removeNth (r.insertNth (α := fun _ => M) b (i.insertNth (α := fun _ => M) 0 v))) := by
  ext a
  simp only [ContinuousLinearMap.flip_apply,pairSlice_apply,sliceAt_apply,Fin.insertNth_removeNth]
  rw [← Fin.insertNth_update,Fin.update_insertNth]

lemma normalAt_pairSlice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) :
    pairSlice (normalAt e f r) r i v=(operatorNormalPart e).comp (pairSlice f r i v) := by
  ext a b
  simp only [pairSlice_apply,ContinuousLinearMap.comp_apply,normalAt_insert]
  congr 1

lemma normalAt_retains_factored_slice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M)
    (H : X → Type v) [∀ z,NormedAddCommGroup (H z)] [∀ z,InnerProductSpace ℂ (H z)]
    [∀ z,CompleteSpace (H z)]
    (α : ∀ z,H z →L[ℂ] StrongDual ℂ M) (β : ∀ z,M →L[ℂ] H z)
    (hfac : ∀ z a b,predualEmbedding e z (f (r.insertNth b (i.insertNth a v)))=
      α z (β z b) a)
    (hN : ∀ w,HasPreadjoint e (sliceAt f (r.succAbove i) w)) (b : M) :
    HasPreadjoint e ((pairSlice (normalAt e f r) r i v).flip b) := by
  rw [normalAt_pairSlice]
  apply operator_bilinear_normalization e (pairSlice f r i v) H α β
  · exact hfac
  · intro c
    rw [pairSlice_flip]
    exact hN _

omit [CompleteSpace X] in
lemma HasPreadjoint.smul {T : M →L[ℂ] M} (hT : HasPreadjoint e T) (c : ℂ) :
    HasPreadjoint e (c • T) := by
  rw [hasPreadjoint_iff_scalar] at hT ⊢
  intro z
  simpa only [ContinuousLinearMap.comp_smul] using (normalDual e).smul_mem c (hT z)

omit [CompleteSpace X] in
lemma HasPreadjoint.zero : HasPreadjoint e (0 : M →L[ℂ] M) := by
  rw [hasPreadjoint_iff_scalar]
  intro z
  simpa only [ContinuousLinearMap.comp_zero] using (normalDual e).zero_mem

omit [CompleteSpace X] in
lemma HasPreadjoint.sum {ι : Type*} (s : Finset ι) (T : ι → M →L[ℂ] M)
    (hT : ∀ j ∈ s,HasPreadjoint e (T j)) : HasPreadjoint e (∑ j ∈ s,T j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasPreadjoint.zero e
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hT a (Finset.mem_insert_self _ _)).add e
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

lemma leftCoboundary_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    HasPreadjoint e (sliceAt (leftCoboundary h) i.castSucc v) := by
  by_cases hzero : i.val=0
  · have hie : i=0 := Fin.ext hzero
    subst i
    have hs : sliceAt (leftCoboundary h) (0:Fin (n+2)) v=
        (ContinuousLinearMap.mul ℂ M).flip (h v) := by
      ext a
      simp only [sliceAt_apply,leftCoboundary_apply,ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply',Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
    rw [show (0:Fin (n+1)).castSucc=(0:Fin (n+2)) from rfl,hs]
    exact (HochschildSakai.abstract_multiplication_normal e).2 _
  · have hip : (0 : ℕ) < (i : ℕ) := by omega
    rw [sliceAt_left h i hip v]
    exact ((HochschildSakai.abstract_multiplication_normal e).1 _).comp e
      (hN _ (by dsimp; omega) _)

lemma middleCoboundary_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    ∀ j : Fin (n+1),j.val<r → HasPreadjoint e (sliceAt (middleCoboundary h j) i.castSucc v) := by
  rw [Fin.forall_iff_succAbove i]
  constructor
  · intro hir
    rw [sliceAt_middle_same]
    exact (hN _ hir _).comp e ((HochschildSakai.abstract_multiplication_normal e).2 _)
  · intro j hj
    rcases lt_trichotomy (j.val+1) i.val with hij|hij|hij
    · rw [sliceAt_middle_before h i j hij v]
      exact hN _ (by dsimp; omega) _
    · rw [sliceAt_middle_before_boundary h i j hij v]
      exact (hN j.castSucc (by simp only [Fin.val_castSucc]; omega) _).comp e
        ((HochschildSakai.abstract_multiplication_normal e).1 _)
    · have hle : i.val≤j.val := by omega
      rw [sliceAt_middle_after h i j hle v]
      have hs : i.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [hs] at hj
      exact hN _ (by simp only [Fin.val_succ] at hj; omega) _

lemma prefixDifferential_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    HasPreadjoint e (sliceAt (prefixDifferential h r) i.castSucc v) := by
  rw [prefixDifferential,sliceAt_add,sliceAt_sum]
  apply (leftCoboundary_before_normal e h r hN i hi v).add e
  apply HasPreadjoint.sum e
  intro j _
  by_cases hj : j.val<r
  · rw [ite_eq_left hj,sliceAt_smul]
    exact (middleCoboundary_before_normal e h r hN i hi v j hj).smul e _
  · rw [ite_eq_right hj,sliceAt_zero]
    exact HasPreadjoint.zero e

lemma prefix_middle_unit_other {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val≤r)
    (v : Fin (n+1) → M) (j : Fin n) :
    (if (i.succAbove j).val<r then ((-1:ℂ)^((i.succAbove j).val+1)) •
      h (mergeInputs (i.castSucc.insertNth 1 v) (i.succAbove j)) else 0)=
    if j.val+1=i.val then ((-1:ℂ)^i.val) • h v else 0 := by
  rcases lt_trichotomy (j.val+1) i.val with hij|hij|hij
  · have hz : h (mergeInputs (i.castSucc.insertNth (1:M) v) (i.succAbove j))=0 := by
      rw [merge_insert_before v i 1 j hij]
      exact hU _ (by dsimp; omega) _
    rw [hz]
    simp only [smul_zero,ite_self,show ¬j.val+1=i.val by omega,ite_false]
  · have hs : i.succAbove j=j.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)
    have hjr : (i.succAbove j).val<r := by rw [hs]; simp only [Fin.val_castSucc]; omega
    rw [ite_eq_left hjr,merge_insert_prev v i j hij 1,hs]
    simp only [Fin.val_castSucc,hij,ite_true,mul_one,Function.update_eq_self]
  · have hle : i.val≤j.val := by omega
    rw [ite_eq_right (by omega : ¬j.val+1=i.val)]
    split_ifs with hjr
    · rw [merge_insert_after v i 1 j hle]
      have hs : i.succAbove j=j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hle)
      rw [hs] at hjr
      rw [hU _ (by simp only [Fin.val_succ] at hjr; dsimp; omega) _,smul_zero]
    · rfl

lemma prefixDifferential_unit {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    prefixDifferential h r (i.castSucc.insertNth 1 v)=
      ((-1:ℂ)^i.val) • h v +
      if i.val<r then ((-1:ℂ)^(i.val+1)) • h v else 0 := by
  rw [prefixDifferential_apply,Fin.sum_univ_succAbove _ i]
  have hs : mergeInputs (i.castSucc.insertNth (1:M) v) i=v :=
    merge_insert_same v i 1 (by simp)
  rw [hs]
  simp_rw [prefix_middle_unit_other h r hU i hi v]
  by_cases hz : i.val=0
  · have hie : i=0 := Fin.ext hz
    subst i
    simp only [Fin.val_zero,Fin.castSucc_zero,Fin.insertNth_zero',Fin.cons_zero,
      Fin.cons_succ,one_mul,pow_zero,one_smul]
    have hj (j : Fin n) : ¬j.val+1=0 := by omega
    simp only [hj,ite_false,Finset.sum_const_zero,add_zero]
  · have hip : 0 < i.val := by omega
    have hl : (i.castSucc.insertNth (α := fun _ => M) 1 v) 0*
        h (fun j => (i.castSucc.insertNth (α := fun _ => M) 1 v) j.succ)=0 := by
      rw [tail_insert v i 1 hip,hU _ (by dsimp; omega),mul_zero]
    rw [hl,zero_add]
    let b : Fin n := ⟨i.val-1,by omega⟩
    have hj (j : Fin n) : (j.val+1=i.val) ↔ j=b := by
      simp only [Fin.ext_iff,b]
      omega
    simp only [hj,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    abel

lemma prefixDifferential_unit_before {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val<r) (v : Fin (n+1) → M) :
    prefixDifferential h r (i.castSucc.insertNth 1 v)=0 := by
  rw [prefixDifferential_unit h r hU i (by omega) v,ite_eq_left hi,sign_succ,neg_smul,add_neg_cancel]

lemma prefixDifferential_unit_at {n : ℕ} (h : Cochain M (n+1)) (r : Fin (n+1))
    (hU : UnitZeroBefore h r.val) (v : Fin (n+1) → M) :
    prefixDifferential h r.val (r.castSucc.insertNth 1 v)=((-1:ℂ)^r.val) • h v := by
  rw [prefixDifferential_unit h r.val hU r (by rfl) v,ite_eq_right (lt_irrefl _),add_zero]

lemma normalAt_old_slice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (w : Fin (n+1) → M)
    (H : (Fin n → M) → X → Type v)
    [∀ t z,NormedAddCommGroup (H t z)] [∀ t z,InnerProductSpace ℂ (H t z)]
    [∀ t z,CompleteSpace (H t z)]
    (α : ∀ t z,H t z →L[ℂ] StrongDual ℂ M) (β : ∀ t z,M →L[ℂ] H t z)
    (hfac : ∀ t z a b,predualEmbedding e z (f (r.insertNth b (i.insertNth a t)))=
      α t z (β t z b) a)
    (hN : ∀ w,HasPreadjoint e (sliceAt f (r.succAbove i) w)) :
    HasPreadjoint e (sliceAt (normalAt e f r) (r.succAbove i) w) := by
  let v₀ : Fin (n+2) → M := (r.succAbove i).insertNth 0 w
  let q := r.removeNth v₀
  let t := i.removeNth q
  have hq : i.insertNth (α := fun _ => M) 0 t=q := by
    have hz : q i=0 := by
      simp only [q,Fin.removeNth,v₀,Fin.insertNth_apply_same]
    rw [← hz]
    exact Fin.insertNth_self_removeNth i q
  have hv : r.insertNth (α := fun _ => M) (v₀ r) (i.insertNth (α := fun _ => M) 0 t)=v₀ := by
    rw [hq]
    exact Fin.insertNth_self_removeNth r v₀
  have h := normalAt_retains_factored_slice e f r i t (H t) (α t) (β t)
    (hfac t) hN (v₀ r)
  rw [pairSlice_flip,hv] at h
  simpa only [v₀,Fin.removeNth_insertNth] using h

lemma normalAt_before_normal_of_factors {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hN : NormalBefore e f r.val)
    (H : Fin (n+1) → (Fin n → M) → X → Type v)
    [∀ i t z,NormedAddCommGroup (H i t z)] [∀ i t z,InnerProductSpace ℂ (H i t z)]
    [∀ i t z,CompleteSpace (H i t z)]
    (α : ∀ i t z,H i t z →L[ℂ] StrongDual ℂ M) (β : ∀ i t z,M →L[ℂ] H i t z)
    (hfac : ∀ i,i.val<r.val → ∀ t z a b,
      predualEmbedding e z (f (r.insertNth b (i.insertNth a t)))=α i t z (β i t z b) a) :
    NormalBefore e (normalAt e f r) r.val := by
  intro j hj w
  let i : Fin (n+1) := ⟨j.val, by omega⟩
  have hs : r.succAbove i=j := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; exact hj)]
    rfl
  rw [← hs]
  exact normalAt_old_slice e f r i w (H i) (α i) (β i) (hfac i hj)
    (by rw [hs]; exact hN j hj)

lemma insertion_before_normal {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hN : NormalBefore e (normalAt e f r) r.val) :
    NormalBefore e (slotInsertion e f r) r.val := by
  intro i hi v
  have hs : r.succAbove i=i.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def,Fin.val_castSucc] using hi)
  have he : sliceAt (slotInsertion e f r) i v=(pairSlice (normalAt e f r) r i v).flip 1 := by
    ext a
    rfl
  rw [he,pairSlice_flip]
  exact hN _ (by rw [hs]; exact hi) _

lemma slotRemainder_normal {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (hNN : NormalBefore e (normalAt e f r.castSucc) r.val) :
    NormalBefore e (slotRemainder e f r.castSucc) (r.val+1) := by
  have hh := insertion_before_normal e f r.castSucc hNN
  intro j hj v
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hji : i.castSucc=j := rfl
  have hs : sliceAt (slotRemainder e f r.castSucc) j v=
      sliceAt (normalAt e f r.castSucc) j v - ((-1:ℂ)^r.val) •
        sliceAt (prefixDifferential (slotInsertion e f r.castSucc) r.val) j v := by
    ext a
    simpa only [sliceAt_apply,sub_apply,smul_apply,Fin.val_castSucc]
      using slotRemainder_apply e f r.castSucc hr hf hN hU (j.insertNth a v)
  rw [hs]
  apply HasPreadjoint.sub e _
    ((prefixDifferential_before_normal e _ r.val hh i (by dsimp [i]; omega) v).smul e _)
  by_cases hjr : j.val<r.val
  · exact hNN j hjr v
  · have hjr : j=r.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [hjr]
    exact normalAt_normal e f r.castSucc v

lemma slotRemainder_unitZero {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val) :
    UnitZeroBefore (slotRemainder e f r.castSucc) (r.val+1) := by
  have hh := insertion_preserves_unitZero e f r.castSucc hU
  have hn := normalAt_preserves_unitZero e f r.castSucc hU
  intro j hj v
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hji : i.castSucc=j := rfl
  rw [slotRemainder_apply e f r.castSucc hr hf hN hU]
  simp only [Fin.val_castSucc]
  by_cases hjr : j.val<r.val
  · rw [hn j hjr v,← hji,prefixDifferential_unit_before _ r.val hh i hjr v,smul_zero,sub_zero]
  · have hjr : j=r.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [hjr]
    rw [prefixDifferential_unit_at _ r hh v]
    change slotInsertion e f r.castSucc v-(((-1:ℂ)^r.val) • (((-1:ℂ)^r.val) • _))=0
    rw [smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul,sub_self]

theorem slot_step_of_factors {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val)
    (H : Fin (n+1) → (Fin n → M) → X → Type v)
    [∀ i t z,NormedAddCommGroup (H i t z)] [∀ i t z,InnerProductSpace ℂ (H i t z)]
    [∀ i t z,CompleteSpace (H i t z)]
    (α : ∀ i t z,H i t z →L[ℂ] StrongDual ℂ M) (β : ∀ i t z,M →L[ℂ] H i t z)
    (hfac : ∀ i,i.val<r.val → ∀ t z a b,
      predualEmbedding e z (f (r.castSucc.insertNth b (i.insertNth a t)))=
        α i t z (β i t z b) a) :
    ∃ (R : Cochain M (n+2)) (h : Cochain M (n+1)),
      (∀ v,differentialValue R v=0) ∧
      (∀ v,f v=R v+differentialValue h v) ∧ ‖h‖≤4*‖f‖ ∧
      NormalBefore e R (r.val+1) ∧ UnitZeroBefore R (r.val+1) := by
  have hNN := normalAt_before_normal_of_factors e f r.castSucc hN H α β hfac
  exact ⟨slotRemainder e f r.castSucc,slotCorrection e f r.castSucc,
    slotRemainder_cocycle e f r.castSucc hf,slotRemainder_identity e f r.castSucc,
    slotCorrection_norm e f r.castSucc,slotRemainder_normal e f r hr hf hN hU hNN,
    slotRemainder_unitZero e f r hr hf hN hU⟩

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def penultimateSlice {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c : M) : M →L[ℂ] M :=
  (insertLast f c).curryRight v

@[simp] lemma penultimateSlice_apply {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c b : M) :
    penultimateSlice f v c b=f (Fin.snoc (Fin.snoc v b) c) := rfl

lemma differentialValue_snoc_snoc {n : ℕ} (f : Cochain M (n+2))
    (v : Fin (n+1) → M) (b c : M) :
    differentialValue f (Fin.snoc (Fin.snoc v b) c)=
      v 0*f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.succ) b) c)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) •
        f (Fin.snoc (Fin.snoc (mergeInputs v j) b) c))+
      ((-1:ℂ)^(n+1)) •
        f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*b)) c)+
      ((-1:ℂ)^(n+2)) • f (Fin.snoc v (b*c))+
      ((-1:ℂ)^(n+3)) • (f (Fin.snoc v b)*c) := by
  rw [differentialValue_snoc,Fin.sum_univ_castSucc]
  have hzero : (Fin.snoc v b : Fin (n+2) → M) 0=v 0 :=
    Fin.snoc_castSucc (α := fun _ => M) b v 0
  simp only [hzero,snoc_succ_tuple,mergeInputs_snoc_castSucc,Fin.val_castSucc,
    mergeInputs_snoc_last,Fin.val_last,snoc_castSucc_tuple,Fin.snoc_last]
  abel

theorem cocycle_last_normal_of_penultimate_normal {n : ℕ}
    (f : Cochain M (n+2)) (hf : ∀ z,differentialValue f z=0)
    (hN : ∀ v c,HasPreadjoint e (penultimateSlice f v c)) :
    ∀ v,HasPreadjoint e (f.curryRight v) := by
  intro v
  let S : M →L[ℂ] M := f.curryRight v
  let P := operatorNormalPart e S
  let L := ContinuousLinearMap.mul ℂ M
  let R := (ContinuousLinearMap.mul ℂ M).flip
  have hrec (b c : M) :
      v 0*f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.succ) b) c)+
      (∑ j : Fin n,((-1:ℂ)^(j.val+1)) •
        f (Fin.snoc (Fin.snoc (mergeInputs v j) b) c))+
      ((-1:ℂ)^(n+1)) •
        f (Fin.snoc (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n)*b)) c)+
      ((-1:ℂ)^(n+2)) • P (b*c)+
      ((-1:ℂ)^(n+3)) • (P b*c)=0 := by
    have hop :
        (L (v 0)).comp (penultimateSlice f (fun i : Fin n => v i.succ) c)+
        (∑ j : Fin n,((-1:ℂ)^(j.val+1)) • penultimateSlice f (mergeInputs v j) c)+
        ((-1:ℂ)^(n+1)) •
          (penultimateSlice f (fun i : Fin n => v i.castSucc) c).comp (L (v (Fin.last n)))+
        ((-1:ℂ)^(n+2)) • S.comp (R c)+
        ((-1:ℂ)^(n+3)) • (R c).comp S=0 := by
      ext x
      simpa only [L,R,S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',
        ContinuousLinearMap.flip_apply,penultimateSlice_apply,add_apply,
        sum_apply,smul_apply,zero_apply,ContinuousMultilinearMap.curryRight_apply,
        differentialValue_snoc_snoc] using hf (Fin.snoc (Fin.snoc v x) c)
    have h := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T b) hop
    dsimp only [L,R] at h
    simp only [map_add,map_sum,map_smul,map_zero,add_apply,sum_apply,smul_apply,zero_apply,
      operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).1 (v 0)),
      operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).2 c),
      operatorNormalPart_comp_left,operatorNormalPart_comp_right,
      operatorNormalPart_fixes e _ (hN _ _),ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,penultimateSlice_apply] at h
    exact h
  have hmodule (c : M) : (S-P) c=(S-P) 1*c := by
    have h := hf (Fin.snoc (Fin.snoc v (1:M)) c)
    rw [differentialValue_snoc_snoc] at h
    have h' := hrec 1 c
    rw [sign_succ (n+2)] at h h'
    simp only [one_mul,neg_smul] at h h'
    have hh : ((-1:ℂ)^(n+2)) • ((S-P) c-(S-P) 1*c)=0 := by
      simp only [S,sub_apply,ContinuousMultilinearMap.curryRight_apply,sub_mul,smul_sub]
      linear_combination (norm := module) h-h'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (by norm_num)))
  have he : S-P=ContinuousLinearMap.mul ℂ M ((S-P) 1) := by
    ext c
    exact hmodule c
  have hz : operatorNormalPart e (S-P)=0 := by
    rw [map_sub,operatorNormalPart_fixes e P (operatorNormalPart_normal e S),sub_self]
  rw [operatorNormalPart_fixes e (S-P) (by
    rw [he]
    exact (HochschildSakai.abstract_multiplication_normal e).1 _)] at hz
  have hSP : S=P := sub_eq_zero.mp hz
  change HasPreadjoint e S
  rw [hSP]
  exact operatorNormalPart_normal e S

end BoundedHochschild

end

end OAI
