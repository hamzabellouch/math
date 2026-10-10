import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.InteriorHomotopy
import OAI.Analysis.TracialCohomology.SlotHomotopy

namespace OAI

/-! Hilbert factorization for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable (M : Type u) [CStarAlgebra M]

structure SharedHilbertFactor (B : M →L[ℂ] StrongDual ℂ M) where
  H : Type u
  group : NormedAddCommGroup H
  inner : InnerProductSpace ℂ H
  complete : CompleteSpace H
  left : H →L[ℂ] StrongDual ℂ M
  right : M →L[ℂ] H
  pairing : ∀ a b,B a b=left (right b) a

attribute [instance] SharedHilbertFactor.group SharedHilbertFactor.inner SharedHilbertFactor.complete

def SharedHilbertFactorizationGoal : Prop :=
  ∀ B : M →L[ℂ] StrongDual ℂ M,Nonempty (SharedHilbertFactor M B)

end HochschildNormalPart

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma firstRemainder_before_normal {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) : NormalBefore e (firstNormalRemainderN e f) 1 := by
  intro i hi v
  have he : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  subst i
  have hs : sliceAt (firstNormalRemainderN e f) 0 v=firstSliceN (normalFirst e f) v-
      (ContinuousLinearMap.mul ℂ M).flip (normalFirst e f (Fin.cons 1 v)) := by
    ext a
    simp only [sliceAt_apply,sub_apply,firstSliceN_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply',Fin.insertNth_zero']
    simpa only [Fin.cons_zero,Fin.cons_succ] using firstNormalRemainderN_apply e f hf (Fin.cons a v)
  rw [hs]
  exact (normalFirst_normal e f v).sub e ((HochschildSakai.abstract_multiplication_normal e).2 _)

lemma firstRemainder_before_unitZero {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) : UnitZeroBefore (firstNormalRemainderN e f) 1 := by
  intro i hi v
  have he : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  subst i
  rw [Fin.insertNth_zero']
  exact firstNormalRemainderN_one e f hf v

lemma slot_step_from_factor_data (factors : ∀ B : M →L[ℂ] StrongDual ℂ M,SharedHilbertFactor M B)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val) :
    ∃ (R : Cochain M (n+2)) (h : Cochain M (n+1)),
      (∀ v,differentialValue R v=0) ∧
      (∀ v,f v=R v+differentialValue h v) ∧ ‖h‖≤4*‖f‖ ∧
      NormalBefore e R (r.val+1) ∧ UnitZeroBefore R (r.val+1) := by
  let B (i : Fin (n+1)) (t : Fin n → M) (z : X) : M →L[ℂ] StrongDual ℂ M :=
    (ContinuousLinearMap.compL ℂ M M ℂ (predualEmbedding e z)).comp (pairSlice f r.castSucc i t)
  let D (i : Fin (n+1)) (t : Fin n → M) (z : X) := factors (B i t z)
  exact slot_step_of_factors e f r hr hf hN hU (fun i t z => (D i t z).H)
    (fun i t z => (D i t z).left) (fun i t z => (D i t z).right)
    (fun i _ t z a b => (D i t z).pairing a b)

theorem normal_before_from_factors
    (factors : ∀ B : M →L[ℂ] StrongDual ℂ M,SharedHilbertFactor M B)
    {n : ℕ} (f : Cochain M (n+2)) (hf : ∀ v,differentialValue f v=0)
    (r : ℕ) (hr : 1≤r) (hrn : r≤n+1) :
    ∃ (F : Cochain M (n+2)) (b : Cochain M (n+1)),
      (∀ v,differentialValue F v=0) ∧
      (∀ v,f v=F v+differentialValue b v) ∧
      NormalBefore e F r ∧ UnitZeroBefore F r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r=0
    · subst r
      exact ⟨firstNormalRemainderN e f,firstNormalCorrectionN e f,
        firstNormalRemainderN_cocycle e f hf,firstNormalRemainderN_identity e f,
        firstRemainder_before_normal e f hf,firstRemainder_before_unitZero e f hf⟩
    · obtain ⟨F,b,hFc,hid,hFN,hFU⟩ := ih (by omega) (by omega)
      let i : Fin (n+1) := ⟨r,by omega⟩
      obtain ⟨R,h,hRc,hid',_,hRN,hRU⟩ :=
        slot_step_from_factor_data e factors F i (by dsimp [i]; omega) hFc hFN hFU
      refine ⟨R,b+h,hRc,?_,hRN,hRU⟩
      intro v
      rw [hid v,hid' v,differentialValue_add]
      abel

lemma penultimateSlice_eq_sliceAt {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (c : M) :
    penultimateSlice f v c=sliceAt f (Fin.last n).castSucc (Fin.snoc v c) := by
  ext a
  rw [penultimateSlice_apply,sliceAt_apply]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rw [tupleInsert_gt _ _ _ _ (by simp)]
    symm
    exact Fin.snoc_last (α := fun _ => M) c v
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.insertNth_apply_same]
    · rw [Fin.snoc_castSucc,Fin.snoc_castSucc,tupleInsert_lt _ _ _ _ (by simp)]
      symm
      exact Fin.snoc_castSucc (α := fun _ => M) c v k

lemma all_normal_of_before_penultimate {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0) (hN : NormalBefore e f (n+1)) :
    ∀ (i : Fin (n+2)) v,HasPreadjoint e (sliceAt f i v) := by
  have hpen (v : Fin n → M) (c : M) : HasPreadjoint e (penultimateSlice f v c) := by
    rw [penultimateSlice_eq_sliceAt]
    exact hN _ (by simp) _
  have hlast := cocycle_last_normal_of_penultimate_normal e f hf hpen
  intro i v
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : sliceAt f (Fin.last (n+1)) v=f.curryRight v := by
      ext a
      simp only [sliceAt_apply,Fin.insertNth_last',ContinuousMultilinearMap.curryRight_apply]
    rw [he]
    exact hlast v
  · exact hN j.castSucc j.isLt v

def SeparatelyNormal {M X : Type*} [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ} (f : Cochain M n) : Prop :=
  ∀ (i : Fin n) (v : Fin n → M) (z : X), ∃ w : X,
    ∀ a : M, e.symm (f (Function.update v i a)) z=e.symm a w

omit [CompleteSpace X] in
lemma separatelyNormal_iff_slices {n : ℕ} (f : Cochain M (n+1)) :
    SeparatelyNormal e f ↔ ∀ i v,HasPreadjoint e (sliceAt f i v) := by
  constructor
  · intro h i v z
    obtain ⟨w,hw⟩ := h i (i.insertNth 0 v) z
    refine ⟨w,fun a => ?_⟩
    simpa only [Fin.update_insertNth,sliceAt_apply] using hw a
  · intro h i v z
    obtain ⟨w,hw⟩ := h i (i.removeNth v) z
    refine ⟨w,fun a => ?_⟩
    simpa only [sliceAt_apply,Fin.insertNth_removeNth] using hw a

theorem normal_reduction_from_factor_data
    (factors : ∀ B : M →L[ℂ] StrongDual ℂ M,SharedHilbertFactor M B)
    {n : ℕ} (f : Cochain M (n+2)) (hf : ∀ v,differentialValue f v=0) :
    ∃ (F : Cochain M (n+2)) (b : Cochain M (n+1)),
      SeparatelyNormal e F ∧
      (∀ v,differentialValue F v=0) ∧
      (∀ v,f v=F v+differentialValue b v) := by
  obtain ⟨F,b,hFc,hid,hFN,_⟩ := normal_before_from_factors e factors f hf (n+1) (by omega) (by rfl)
  exact ⟨F,b,(separatelyNormal_iff_slices e F).mpr
    (all_normal_of_before_penultimate e F hFc hFN),hFc,hid⟩

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def BilinearNormalPartPreservation : Prop :=
  ∀ f : Cochain M 2, (∀ v,HasPreadjoint e (firstSliceN f v)) →
    ∀ v,HasPreadjoint e (firstSliceN (normalLast e f) v)

def bilinearCochain (B : M →L[ℂ] M →L[ℂ] M) : Cochain M 2 :=
  ((continuousMultilinearCurryFin1 ℂ M (M →L[ℂ] M)).symm B).uncurryRight

@[simp] lemma bilinearCochain_apply (B : M →L[ℂ] M →L[ℂ] M) (v : Fin 2 → M) :
    bilinearCochain B v=B (v 0) (v 1) := rfl

lemma bilinearCochain_firstSlice (B : M →L[ℂ] M →L[ℂ] M) (v : Fin 1 → M) :
    firstSliceN (bilinearCochain B) v=B.flip (v 0) := by
  ext a
  rw [firstSliceN_apply]
  rfl

lemma bilinearCochain_normalLast (B : M →L[ℂ] M →L[ℂ] M) :
    normalLast e (bilinearCochain B)=bilinearCochain ((operatorNormalPart e).comp B) := by
  ext v
  simp only [normalLast_apply]
  congr 1

lemma bilinear_preservation_iff : BilinearNormalPartPreservation e ↔
    ∀ (B : M →L[ℂ] M →L[ℂ] M), (∀ b,HasPreadjoint e (B.flip b)) →
      ∀ b,HasPreadjoint e (((operatorNormalPart e).comp B).flip b) := by
  constructor
  · intro h B hn b
    have h' := h (bilinearCochain B) (fun v => by
      rw [bilinearCochain_firstSlice]
      exact hn _) (fun _ => b)
    rwa [bilinearCochain_normalLast,bilinearCochain_firstSlice] at h'
  · intro h f hn v
    let B : M →L[ℂ] M →L[ℂ] M := (continuousMultilinearCurryFin1 ℂ M (M →L[ℂ] M)) f.curryRight
    have hf : bilinearCochain B=f := by
      unfold bilinearCochain B
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact ContinuousMultilinearMap.uncurry_curryRight f
    rw [← hf,bilinearCochain_normalLast,bilinearCochain_firstSlice]
    apply h B
    intro b
    have hn' := hn (fun _ => b)
    rwa [← hf,bilinearCochain_firstSlice] at hn'

lemma normalAt_old_slice_of_preservation
    (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (w : Fin (n+1) → M)
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
  have h := (bilinear_preservation_iff e).mp hP (pairSlice f r i t)
    (fun b => by rw [pairSlice_flip]; exact hN _) (v₀ r)
  rw [← normalAt_pairSlice,pairSlice_flip,hv] at h
  simpa only [v₀,Fin.removeNth_insertNth] using h

lemma normalAt_before_normal_of_preservation
    (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (hN : NormalBefore e f r.val) :
    NormalBefore e (normalAt e f r) r.val := by
  intro j hj w
  let i : Fin (n+1) := ⟨j.val,by omega⟩
  have hs : r.succAbove i=j := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; exact hj)]
    rfl
  rw [← hs]
  exact normalAt_old_slice_of_preservation e hP f r i w (by rw [hs]; exact hN j hj)

lemma slot_step_of_preservation (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+1))
    (hr : 0<r.val) (hf : ∀ v,differentialValue f v=0)
    (hN : NormalBefore e f r.val) (hU : UnitZeroBefore f r.val) :
    ∃ (R : Cochain M (n+2)) (h : Cochain M (n+1)),
      (∀ v,differentialValue R v=0) ∧
      (∀ v,f v=R v+differentialValue h v) ∧ ‖h‖≤4*‖f‖ ∧
      NormalBefore e R (r.val+1) ∧ UnitZeroBefore R (r.val+1) := by
  have hNN := normalAt_before_normal_of_preservation e hP f r.castSucc hN
  exact ⟨slotRemainder e f r.castSucc,slotCorrection e f r.castSucc,
    slotRemainder_cocycle e f r.castSucc hf,slotRemainder_identity e f r.castSucc,
    slotCorrection_norm e f r.castSucc,slotRemainder_normal e f r hr hf hN hU hNN,
    slotRemainder_unitZero e f r hr hf hN hU⟩

theorem normal_before_of_preservation (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (hf : ∀ v,differentialValue f v=0)
    (r : ℕ) (hr : 1≤r) (hrn : r≤n+1) :
    ∃ (F : Cochain M (n+2)) (b : Cochain M (n+1)),
      (∀ v,differentialValue F v=0) ∧
      (∀ v,f v=F v+differentialValue b v) ∧
      NormalBefore e F r ∧ UnitZeroBefore F r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r=0
    · subst r
      exact ⟨firstNormalRemainderN e f,firstNormalCorrectionN e f,
        firstNormalRemainderN_cocycle e f hf,firstNormalRemainderN_identity e f,
        firstRemainder_before_normal e f hf,firstRemainder_before_unitZero e f hf⟩
    · obtain ⟨F,b,hFc,hid,hFN,hFU⟩ := ih (by omega) (by omega)
      let i : Fin (n+1) := ⟨r,by omega⟩
      obtain ⟨R,h,hRc,hid',_,hRN,hRU⟩ :=
        slot_step_of_preservation e hP F i (by dsimp [i]; omega) hFc hFN hFU
      refine ⟨R,b+h,hRc,?_,hRN,hRU⟩
      intro v
      rw [hid v,hid' v,differentialValue_add]
      abel

theorem normal_reduction_of_bilinear_preservation
    (hP : BilinearNormalPartPreservation e)
    {n : ℕ} (f : Cochain M (n+2)) (hf : ∀ v,differentialValue f v=0) :
    ∃ (F : Cochain M (n+2)) (b : Cochain M (n+1)),
      SeparatelyNormal e F ∧
      (∀ v,differentialValue F v=0) ∧
      (∀ v,f v=F v+differentialValue b v) := by
  obtain ⟨F,b,hFc,hid,hFN,_⟩ := normal_before_of_preservation e hP f hf (n+1) (by omega) (by rfl)
  exact ⟨F,b,(separatelyNormal_iff_slices e F).mpr
    (all_normal_of_before_penultimate e F hFc hFN),hFc,hid⟩

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u

def AnalyticProducerGoal : Prop :=
  ∀ (M X : Type u) [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (B : M →L[ℂ] M →L[ℂ] M),
    (∀ b, HasPreadjoint e (B.flip b)) →
      ∀ b, HasPreadjoint e (((operatorNormalPart e).comp B).flip b)

end BoundedHochschild

end

end OAI
