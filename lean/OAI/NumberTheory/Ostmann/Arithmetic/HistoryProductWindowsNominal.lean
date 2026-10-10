import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindows
import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateLabels

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction InitialCoordinatesTemplate

theorem pruned_append (T U : List SourceSlot) (l : ℕ) :
    pruned (T++U) l = pruned T l ++ pruned U l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [pruned,ih,Template.remainder,List.filter_append]

theorem remainder_sourceBlock (j off n : ℕ) (r : SlotRole) :
    Template.remainder j (sourceBlock off n r) =
      if r = .compensation j then [] else sourceBlock off n r := by
  have hr : ∀q∈sourceBlock off n r,q.role=r := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    rfl
  unfold Template.remainder
  by_cases he : r = .compensation j
  · rw [ite_eq_left he]
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    simp only [hr q hq,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,not_false_eq_true]
  · rw [ite_eq_right he]
    apply List.filter_eq_self.mpr
    intro q hq
    simpa only [hr q hq] using (decide_eq_true he)

theorem extracted_sourceBlock (j off n : ℕ) (r : SlotRole) :
    Template.extracted j (sourceBlock off n r) =
      if r = .compensation j then sourceBlock off n r else [] := by
  have hr : ∀q∈sourceBlock off n r,q.role=r := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    rfl
  unfold Template.extracted
  by_cases he : r = .compensation j
  · rw [ite_eq_left he]
    apply List.filter_eq_self.mpr
    intro q hq
    simp only [hr q hq,he,decide_true]
  · rw [ite_eq_right he]
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    simp only [hr q hq,he,decide_false,Bool.false_eq_true,not_false_eq_true]

theorem pruned_sourceBlock_bulk (off n l : ℕ) :
    pruned (sourceBlock off n .bulk) l = sourceBlock off n .bulk := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pruned,ih,remainder_sourceBlock]; simp

theorem pruned_sourceBlock_top (off n l : ℕ) :
    pruned (sourceBlock off n .top) l = sourceBlock off n .top := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pruned,ih,remainder_sourceBlock]; simp

theorem pruned_sourceBlock_comp (off n j l : ℕ) (hj : 0<j) :
    pruned (sourceBlock off n (.compensation j)) l =
      if l<j then sourceBlock off n (.compensation j) else [] := by
  induction l with
  | zero => simp only [pruned,ite_eq_left hj]
  | succ l ih =>
    rw [pruned,ih]
    by_cases hl : l<j
    · rw [ite_eq_left hl,remainder_sourceBlock]
      by_cases he : j=l+1
      · simp [he]
      · have hlj : l+1<j := by omega
        simp [he,hlj]
    · have hlj : ¬l+1<j := by omega
      simp [hl,hlj,Template.remainder]

theorem sourceSum_fixedCenter_bulk (center : ℕ → ℝ) (off n : ℕ) :
    sourceSum (fixedCenter center) (sourceBlock off n .bulk) = 0 := by
  simp [sourceSum,sourceBlock,fixedCenter,List.map_ofFn,Function.comp_def]

theorem sourceSum_fixedCenter_top (b : ℕ) (center : ℕ → ℝ) :
    sourceSum (fixedCenter center) (sourceBlock (2*b) 6 .top) =
      ∑h,∑i,topCenters b center h i := by
  calc
    _ = ∑i : Fin 6,center (2*b+i.val) := by
      simp only [sourceSum,sourceBlock,List.map_ofFn,List.sum_ofFn,Function.comp_def]
      apply Finset.sum_congr rfl
      intro i _
      simp [fixedCenter]
    _ = ∑h : Bool,∑i : Fin 3,center (2*b+(halfEquiv 3 (h,i)).val) := by
      exact ((halfEquiv 3).sum_comp (fun i => center (2*b+i.val))).symm.trans
        (Fintype.sum_prod_type _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro i _
      unfold topCenters
      rw [halfEquiv_val]
      congr 1
      omega

theorem sourceSum_fixedCenter_comp (b j : ℕ) (center : ℕ → ℝ) :
    sourceSum (fixedCenter center) (sourceBlock (2*b+6+4*j) 4 (.compensation (j+1))) =
      ∑h : Bool,∑i : Fin 2,center (2*b+6+4*j+(if h then 2 else 0)+i.val) := by
  calc
    _ = ∑i : Fin 4,center (2*b+6+4*j+i.val) := by
      simp only [sourceSum,sourceBlock,List.map_ofFn,List.sum_ofFn,Function.comp_def]
      apply Finset.sum_congr rfl
      intro i _
      simp [fixedCenter]
    _ = ∑h : Bool,∑i : Fin 2,center (2*b+6+4*j+(halfEquiv 2 (h,i)).val) := by
      exact ((halfEquiv 2).sum_comp (fun i => center (2*b+6+4*j+i.val))).symm.trans
        (Fintype.sum_prod_type _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro i _
      rw [halfEquiv_val]
      congr 1
      omega

def typeCenter (b j : ℕ) (center : ℕ → ℝ) : ℝ :=
  ∑h : Bool,∑i : Fin 2,center (2*b+6+4*j+(if h then 2 else 0)+i.val)

theorem sourceSum_pruned_initial (b k l : ℕ) (center : ℕ → ℝ) :
    sourceSum (fixedCenter center) (pruned (Template.initial (2*b) k) l) =
      (∑h,∑i,topCenters b center h i) +
      ∑j∈Finset.range k, if l<j+1 then typeCenter b j center else 0 := by
  induction k with
  | zero =>
    rw [initial_zero,pruned_append,pruned_sourceBlock_bulk,pruned_sourceBlock_top,
      sourceSum_append,sourceSum_fixedCenter_bulk,sourceSum_fixedCenter_top]
    simp
  | succ k ih =>
    rw [initial_succ,pruned_append,sourceSum_append,ih,pruned_sourceBlock_comp _ _ _ _ (by omega),Finset.sum_range_succ]
    by_cases hl : l<k+1
    · rw [ite_eq_left hl,ite_eq_left hl,sourceSum_fixedCenter_comp]
      dsimp [typeCenter]
      ring
    · simp [hl,sourceSum]

theorem sourceSum_extracted_pruned_initial (b k l j : ℕ) (center : ℕ → ℝ) :
    sourceSum (fixedCenter center) (Template.extracted j (pruned (Template.initial (2*b) k) l)) =
      ∑n∈Finset.range k, if l<n+1 ∧ n+1=j then typeCenter b n center else 0 := by
  induction k with
  | zero =>
    rw [initial_zero,pruned_append,pruned_sourceBlock_bulk,pruned_sourceBlock_top]
    simp only [Template.extracted,List.filter_append]
    change sourceSum (fixedCenter center)
      (Template.extracted j (sourceBlock 0 (2*b) .bulk) ++
        Template.extracted j (sourceBlock (2*b) 6 .top)) = _
    rw [sourceSum_append,extracted_sourceBlock,extracted_sourceBlock]
    simp [sourceSum]
  | succ k ih =>
    rw [initial_succ,pruned_append]
    simp only [Template.extracted,List.filter_append]
    change sourceSum (fixedCenter center)
      (Template.extracted j (pruned (Template.initial (2*b) k) l) ++
        Template.extracted j (pruned (sourceBlock (2*b+6+4*k) 4 (.compensation (k+1))) l)) = _
    rw [sourceSum_append,ih,pruned_sourceBlock_comp _ _ _ _ (by omega),Finset.sum_range_succ]
    by_cases hl : l<k+1
    · rw [ite_eq_left hl,extracted_sourceBlock]
      by_cases hj : k+1=j
      · subst j
        simp only [ite_true, hl, and_true]
        congr 1
        exact sourceSum_fixedCenter_comp b k center
      · simp [hj,hl,sourceSum]
    · simp [hl,Template.extracted,sourceSum]

theorem removedCenter_eq_typeCenter (b k l : ℕ) (hl : l<k) (center : ℕ → ℝ) :
    removedCenter b k l center = typeCenter b l center := by
  unfold removedCenter
  rw [sourceSum_extracted_pruned_initial]
  have hp : ∀n, (l<n+1 ∧ n+1=l+1) ↔ n=l := by intro n; omega
  simp only [hp]
  simp [Finset.mem_range,hl]

theorem inheritedCenter_eq_arrays (b k l : ℕ) (center : ℕ → ℝ) :
    inheritedCenter b k l center = (∑h,∑i,topCenters b center h i) +
      ∑j∈Finset.Ico (l+1) k, typeCenter b j center := by
  unfold inheritedCenter
  rw [sourceSum_pruned_initial]
  congr 1
  rw [←Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  omega

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
