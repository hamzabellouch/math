import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedFlatTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
local instance physicalTensorPatchMeasurableSpace :
    MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _
local instance physicalTensorPatchBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

def sourceFlatPatch (i j : Fin 4) : Set (Fin 3 → ℝ) :=
  sourceCollarPiece i j '' sourceExtendedBox (-(1:ℝ)/100) (1/100)

lemma isCompact_sourceFlatPatch (i j : Fin 4) : IsCompact (sourceFlatPatch i j) :=
  isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous

lemma continuousAt_sourceCollarInverse_patch (i j : Fin 4) {y : Fin 3 → ℝ}
    (hy : y∈sourceFlatPatch i j) : ContinuousAt (sourceCollarInverse i j) y := by
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
  have hr : 0<sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j ht hj).1
  have hrad := sourceCollarPiece_radial_pos i j hr.le hi
  have htime := sourceCollarPiece_time_pos i j hr.le (by linarith [ht.2] : x 0≤1) hi hj
  have hc : Continuous sourceCollarTime := by
    unfold sourceCollarTime sourceCrossCoordinates sourceRadial
    fun_prop
  have hcR : Continuous sourceRadial := by unfold sourceRadial; fun_prop
  have hcX : Continuous sourceCrossCoordinates := by
    unfold sourceCrossCoordinates sourceRadial
    fun_prop
  unfold sourceCollarInverse
  apply continuousAt_pi.mpr
  intro k
  fin_cases k
  · exact hc.continuousAt
  · apply ContinuousAt.div
    · unfold squareFaceParameter
      fun_prop
    · exact hcR.continuousAt
    · rw [hrad]
      exact hr.ne'
  · apply ContinuousAt.div
    · exact ((show Continuous (squareFaceParameter j) by
        unfold squareFaceParameter; fun_prop).comp hcX).continuousAt
    · exact continuousAt_const.sub hc.continuousAt
    · rw [htime]
      linarith [ht.2]

lemma continuousOn_attachedPhysicalFlatTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) : ContinuousOn (attachedPhysicalFlatTensor s a i j) (sourceFlatPatch i j) := by
  apply (continuousOn_attachedFlatTensor s ha i j).comp
    (fun y hy => (continuousAt_sourceCollarInverse_patch i j hy).continuousWithinAt)
  rintro _ ⟨x,hx,rfl⟩
  simpa only [sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx] using hx

def attachedPatchTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  by classical exact if y∈sourceFlatPatch i j then attachedPhysicalFlatTensor s a i j y else 1

lemma measurable_attachedPatchTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) : Measurable (attachedPatchTensor s a i j) := by
  classical
  exact (continuousOn_attachedPhysicalFlatTensor s ha i j).measurable_piecewise
    continuousOn_const (isCompact_sourceFlatPatch i j).isClosed.measurableSet

lemma attachedPatchTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : (attachedPatchTensor s a i j y)ᵀ=attachedPatchTensor s a i j y := by
  classical
  unfold attachedPatchTensor
  split_ifs
  · exact attachedPhysicalFlatTensor_symmetric s a i j y
  · exact Matrix.transpose_one

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
local instance attachedFaceTensorListMeasurableSpace :
    MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _
local instance attachedFaceTensorListBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

def attachedFaceTensorList (s : Fin 3 → ℝ) (a : ℝ) (ks : List (Fin 4 × Fin 4))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact ks.foldr (fun k A => if y∈sourceFlatPatch k.1 k.2 then
    attachedPatchTensor s a k.1 k.2 y else A) 1

lemma attachedFaceTensorList_cons (s : Fin 3 → ℝ) (a : ℝ)
    (k : Fin 4 × Fin 4) (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    attachedFaceTensorList s a (k::ks) y=
      (by classical exact if y∈sourceFlatPatch k.1 k.2 then attachedPatchTensor s a k.1 k.2 y
        else attachedFaceTensorList s a ks y) := by
  classical
  rfl

lemma attachedFaceTensorList_measurable (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (ks : List (Fin 4 × Fin 4)) : Measurable (attachedFaceTensorList s a ks) := by
  classical
  induction ks with
  | nil => exact measurable_const
  | cons k ks ih =>
    exact Measurable.ite (isCompact_sourceFlatPatch k.1 k.2).isClosed.measurableSet
      (measurable_attachedPatchTensor s ha k.1 k.2) ih

lemma attachedFaceTensorList_symmetric (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    (attachedFaceTensorList s a ks y)ᵀ=attachedFaceTensorList s a ks y := by
  classical
  induction ks with
  | nil => exact Matrix.transpose_one
  | cons k ks ih =>
    simp only [attachedFaceTensorList_cons]
    split_ifs
    · exact attachedPatchTensor_symmetric s a k.1 k.2 y
    · exact ih

lemma identity_matrix_energy_bounds : ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ v : Fin 3 → ℝ,
    c*‖v‖^2≤v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv) ∧
      v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv)≤C*‖v‖^2 := by
  have hp (u : Unit) (_ : u∈({()} : Set Unit)) (v : Fin 3 → ℝ) (hv : v≠0) :
      0<v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv) := by
    rw [Matrix.one_mulVec]
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k)))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hv))
  obtain ⟨c,C,hc,hcC,h⟩ := compact_matrix_energy_bounds isCompact_singleton
    (fun _ : Unit => (1 : Matrix (Fin 3) (Fin 3) ℝ)) continuousOn_const hp
  exact ⟨c,C,hc,hcC,h () (mem_singleton ())⟩

lemma attachedFaceTensorList_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (ks : List (Fin 4 × Fin 4)) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
      c*‖v‖^2≤v ⬝ᵥ (attachedFaceTensorList s a ks y*ᵥv) ∧
        v ⬝ᵥ (attachedFaceTensorList s a ks y*ᵥv)≤C*‖v‖^2 := by
  classical
  induction ks with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨c,C,hc,hcC,fun _ => h⟩
  | cons k ks ih =>
    obtain ⟨c,C,hc,hcC,h⟩ := ih
    obtain ⟨d,D,hd,hdD,hk⟩ := attachedPhysicalFlatTensor_elliptic s hs ha k.1 k.2
    refine ⟨min c d,max C D,lt_min hc hd,
      lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩
    intro y v
    simp only [attachedFaceTensorList_cons]
    by_cases hy : y∈sourceFlatPatch k.1 k.2
    · simp only [ite_eq_left hy,attachedPatchTensor]
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hk y hy v).1,
        (hk y hy v).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
    · simp only [ite_eq_right hy]
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,
        (h y v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

lemma attachedFaceTensorList_outside (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∀ k∈ks,y∉sourceFlatPatch k.1 k.2) : attachedFaceTensorList s a ks y=1 := by
  classical
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right (hy k (List.mem_cons_self))]
      using ih (fun l hl => hy l (List.mem_cons_of_mem k hl))

lemma attachedFaceTensorList_local (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧
      attachedFaceTensorList s a ks y=attachedPhysicalFlatTensor s a k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · refine ⟨k,List.mem_cons_self,hk,?_⟩
      simp only [attachedFaceTensorList,List.foldr_cons,ite_eq_left hk,attachedPatchTensor]
    · obtain ⟨l,hl,hy⟩ := hy
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,(List.mem_cons.mp hl).resolve_left
        (fun e => hk (e ▸ hy)),hy⟩
      refine ⟨l,List.mem_cons_of_mem k hl,hly,?_⟩
      simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right hk] using he

def attachedCollarTensor (s : Fin 3 → ℝ) (a : ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  attachedFaceTensorList s a (Finset.univ : Finset (Fin 4 × Fin 4)).toList

theorem attachedCollarTensor_properties (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) :
    Measurable (attachedCollarTensor s a) ∧
      (∀ y,(attachedCollarTensor s a y)ᵀ=attachedCollarTensor s a y) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2≤v ⬝ᵥ (attachedCollarTensor s a y*ᵥv) ∧
          v ⬝ᵥ (attachedCollarTensor s a y*ᵥv)≤C*‖v‖^2) ∧
      (∀ y,(∀ i j,y∉sourceFlatPatch i j) → attachedCollarTensor s a y=1) ∧
      (∀ y,(∃ i j,y∈sourceFlatPatch i j) → ∃ i j,y∈sourceFlatPatch i j ∧
        attachedCollarTensor s a y=attachedPhysicalFlatTensor s a i j y) := by
  refine ⟨attachedFaceTensorList_measurable s ha _,
    attachedFaceTensorList_symmetric s a _,attachedFaceTensorList_elliptic s hs ha _,?_,?_⟩
  · intro y hy
    exact attachedFaceTensorList_outside s a _ y (fun k _ => hy k.1 k.2)
  · rintro y ⟨i,j,hy⟩
    obtain ⟨k,_,hk,he⟩ := attachedFaceTensorList_local s a
      (Finset.univ : Finset (Fin 4 × Fin 4)).toList y ⟨(i,j),by simp,hy⟩
    exact ⟨k.1,k.2,hk,he⟩

end ScalarConductivity

end

end OAI
