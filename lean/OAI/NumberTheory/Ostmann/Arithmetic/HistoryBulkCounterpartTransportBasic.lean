import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCounterpartValue
import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction HistoryOccurrenceVariables HistoryGiantReferenceCounterpart

def redrawRootSmall {l : ℕ} (h : History l) (values : Fin h.root.small.length → ℕ) : List SmallSlot :=
  List.ofFn (fun i => {h.root.small.get i with value := values i})

theorem diagonalRoleKeys_redraw {l : ℕ} (h : History l)
    (values : Fin h.root.small.length → ℕ) (F : Key h → ℝ)
    (hF : ∀ i, F (.inr (.inl i)) = (values i : ℝ)) (pred : SlotRole → Bool) :
    (diagonalRoleKeys h (fun q => pred q.role)).map F =
      ((redrawRootSmall h values).filter (fun q => pred q.role)).map (fun q => (q.value : ℝ)) := by
  simp only [diagonalRoleKeys, redrawRootSmall, List.ofFn_eq_map, List.filter_map,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  exact hF i

theorem diagonalRoleKeys_redraw_cells {l : ℕ} (h : History l)
    (values : Fin h.root.small.length → ℕ) (F : Key h → ℝ)
    (hF : ∀ i, F (.inr (.inl i)) = (values i : ℝ))
    (pred : SlotRole → Bool) (G : ℝ) (center : ℕ → ℝ) :
    (diagonalRoleKeys h (fun q => pred q.role)).map
      (fun i => giantCell (diagonalKeyCenter h G center i) (F i)) =
      ((redrawRootSmall h values).filter (fun q => pred q.role)).map
        (fun q => giantCell (center q.origin) (q.value : ℝ)) := by
  simp only [diagonalRoleKeys, redrawRootSmall, List.ofFn_eq_map, List.filter_map,
    List.map_map, Function.comp_def, diagonalKeyCenter]
  apply List.map_congr_left
  intro i hi
  rw [hF i]

theorem diagonalRootCounterpart_redraw {l : ℕ} (h : History l)
    (values : Fin h.root.small.length → ℕ) (F : Key h → ℝ)
    (hF : ∀ i, F (.inr (.inl i)) = (values i : ℝ)) (Q : ℝ) (hQ : F (.inl true) = Q)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : redrawRootSmall h values = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B G : ℝ) (center : ℕ → ℝ) :
    diagonalRootCounterpart h j A B G center F =
      remainingCounterpartAt sources T j A B G center u y Q := by
  have hfilters := reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ y)
  have hH : ((diagonalHKeys h j).map F).prod =
      Q * (((assignedSlots sources (Template.remainder j T) y).map SmallSlot.value).prod : ℝ) := by
    simp only [diagonalHKeys, List.map_cons, List.prod_cons]
    rw [diagonalRoleKeys_redraw h values F hF (fun r => decide (r ≠ .compensation j)), hQ, hsmall, hfilters.2]
    simp only [Nat.cast_list_prod, List.map_map, Function.comp_def]
  have hU : ((diagonalUKeys h j).map F).prod =
      (((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod : ℝ) := by
    rw [diagonalUKeys, diagonalRoleKeys_redraw h values F hF (fun r => decide (r = .compensation j)), hsmall, hfilters.1]
    simp only [Nat.cast_list_prod, List.map_map, Function.comp_def]
  have hcell : (∏ i : Fin (diagonalCellKeys h j).length,
      giantCell (diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
        (F ((diagonalCellKeys h j).get i))) =
      giantCell G Q *
        (((assignedSlots sources (Template.remainder j T) y).filter
          (fun q => decide (q.role ≠ .bulk))).map
          (fun q => giantCell (center q.origin) (q.value : ℝ))).prod := by
    have he : (∏ i : Fin (diagonalCellKeys h j).length,
        giantCell (diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
          (F ((diagonalCellKeys h j).get i))) =
        ((diagonalCellKeys h j).map (fun i => giantCell (diagonalKeyCenter h G center i) (F i))).prod := by
      rw [← List.prod_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map (diagonalCellKeys h j)
        (fun i => giantCell (diagonalKeyCenter h G center i) (F i))
    rw [he]
    simp only [diagonalCellKeys, List.map_cons, List.prod_cons]
    rw [diagonalRoleKeys_redraw_cells h values F hF
      (fun r => decide (r ≠ .compensation j ∧ r ≠ .bulk)) G center, hQ]
    simp only [diagonalKeyCenter]
    rw [hsmall, reinsert_counterpart_cell_filter sources T j u y]
  unfold diagonalRootCounterpart rootCounterpart counterpartArchimedean
  rw [hH, hU, hcell]
  rfl

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
