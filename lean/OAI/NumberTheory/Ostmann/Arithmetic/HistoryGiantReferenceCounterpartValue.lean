import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCounterpartBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantReferenceCounterpart
open Construction HistoryOccurrenceVariables HistoryPairGiantCoordinates HistoryPairSmoothXi
open HistoryPairPattern HistoryActiveCoordinates

theorem diagonalRootCounterpart_realGiantSample {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : h.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B G : ℝ) (center : ℕ → ℝ) (z : Bool → ℝ) :
    diagonalRootCounterpart h j A B G center (realGiantSample h z) =
      remainingCounterpartAt sources T j A B G center u y (z true) := by
  have hfilters := reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ y)
  have hH : ((diagonalHKeys h j).map (realGiantSample h z)).prod =
      z true * (((assignedSlots sources (Template.remainder j T) y).map SmallSlot.value).prod : ℝ) := by
    simp only [diagonalHKeys,List.map_cons,List.prod_cons,diagonalRoleKeys_realGiantSample,
      realGiantSample]
    rw [hsmall,hfilters.2]
    simp only [Nat.cast_list_prod,List.map_map,Function.comp_def]
  have hU : ((diagonalUKeys h j).map (realGiantSample h z)).prod =
      (((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod : ℝ) := by
    rw [diagonalUKeys,diagonalRoleKeys_realGiantSample,hsmall,hfilters.1]
    simp only [Nat.cast_list_prod,List.map_map,Function.comp_def]
  have hcell : (∏ i : Fin (diagonalCellKeys h j).length,
      giantCell (diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
        (realGiantSample h z ((diagonalCellKeys h j).get i))) =
      giantCell G (z true) *
        (((assignedSlots sources (Template.remainder j T) y).filter
          (fun q => decide (q.role ≠ .bulk))).map
          (fun q => giantCell (center q.origin) (q.value : ℝ))).prod := by
    have he : (∏ i : Fin (diagonalCellKeys h j).length,
        giantCell (diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
          (realGiantSample h z ((diagonalCellKeys h j).get i))) =
        ((diagonalCellKeys h j).map (fun i =>
          giantCell (diagonalKeyCenter h G center i) (realGiantSample h z i))).prod := by
      rw [← List.prod_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map (diagonalCellKeys h j)
        (fun i => giantCell (diagonalKeyCenter h G center i) (realGiantSample h z i))
    rw [he]
    simp only [diagonalCellKeys,List.map_cons,List.prod_cons]
    rw [diagonalRoleKeys_realGiantSample_cells]
    simp only [diagonalKeyCenter,realGiantSample]
    rw [hsmall,reinsert_counterpart_cell_filter sources T j u y]
  unfold diagonalRootCounterpart rootCounterpart counterpartArchimedean
  rw [hH,hU,hcell]
  rfl

theorem pairedRootCounterpart_insertGiants {l : ℕ} (h g : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T))
    (hsmall : g.root.small = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y))
    (A B G : ℝ) (center : ℕ → ℝ) (z : Bool → ℝ) :
    pairedRootCounterpart h g j A B G center (insertGiants h g z) =
      remainingCounterpartAt sources T j A B G center u y (z true) := by
  rw [pairedRootCounterpart_pullback]
  change diagonalRootCounterpart g j A B G center
    (fun i => insertGiants h g z (rightMap h g i)) = _
  rw [insertGiants_rightMap]
  exact diagonalRootCounterpart_realGiantSample g sources T j u y hsmall A B G center z

end Ostmann.Arithmetic.HistoryGiantReferenceCounterpart

end

end OAI
