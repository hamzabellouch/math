import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReferenceCounterpart
open Construction HistoryOccurrenceVariables HistoryPairGiantCoordinates
open scoped BigOperators

def remainingCounterpartAt (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (A B G : ℝ) (center : ℕ → ℝ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T)) (Q : ℝ) : ℝ :=
  (Real.exp A / (Q *
    (((assignedSlots sources (Template.remainder j T) y).map SmallSlot.value).prod : ℝ))) *
    ((((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod : ℝ) / Real.exp B) *
    (giantCell G Q *
      (((assignedSlots sources (Template.remainder j T) y).filter
        (fun q => decide (q.role ≠ .bulk))).map
          (fun q => giantCell (center q.origin) (q.value : ℝ))).prod)

theorem remainingCounterpartAt_sample (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (giant : PrimeSource) (A B G : ℝ) (center : ℕ → ℝ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) :
    remainingCounterpartAt sources T j A B G center u x.2 (x.1.val : ℝ) =
      remainingCounterpart sources T j giant A B G center u x := by
  unfold remainingCounterpartAt remainingCounterpart
  rw [giantCell_of_pos G (by exact_mod_cast (giant.prime _ x.1.property).pos)]
  have hc : (((assignedSlots sources (Template.remainder j T) x.2).filter
      (fun q => decide (q.role ≠ .bulk))).map
      (fun q => giantCell (center q.origin) (q.value : ℝ))).prod =
      (((assignedSlots sources (Template.remainder j T) x.2).filter
      (fun q => decide (q.role ≠ .bulk))).map
      (fun q => smoothPartition (Real.log (q.value : ℝ)-center q.origin))).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro q hq
    exact giantCell_of_pos _ (by exact_mod_cast
      (assignedSlots_prime sources (Template.remainder j T) x.2 q (List.mem_filter.mp hq).1).pos)
  rw [hc]
  simp only [remainingProduct,halfProduct,Nat.cast_mul]

theorem diagonalRoleKeys_realGiantSample {l : ℕ} (h : History l)
    (pred : SmallSlot → Bool) (z : Bool → ℝ) :
    (diagonalRoleKeys h pred).map (realGiantSample h z) =
      (h.root.small.filter pred).map (fun q => (q.value : ℝ)) := by
  have he : (List.finRange h.root.small.length).map h.root.small.get = h.root.small := by
    simpa only [← List.ofFn_eq_map] using List.ofFn_get h.root.small
  conv_rhs => rw [← he]
  simp only [diagonalRoleKeys,List.filter_map,List.map_map]
  simp only [Function.comp_def,realGiantSample,integerSample,Int.cast_natCast]

theorem diagonalRoleKeys_realGiantSample_cells {l : ℕ} (h : History l)
    (pred : SmallSlot → Bool) (z : Bool → ℝ) (G : ℝ) (center : ℕ → ℝ) :
    (diagonalRoleKeys h pred).map
      (fun i => giantCell (diagonalKeyCenter h G center i) (realGiantSample h z i)) =
      (h.root.small.filter pred).map (fun q => giantCell (center q.origin) (q.value : ℝ)) := by
  have he : (List.finRange h.root.small.length).map h.root.small.get = h.root.small := by
    simpa only [← List.ofFn_eq_map] using List.ofFn_get h.root.small
  conv_rhs => rw [← he]
  simp only [diagonalRoleKeys,List.filter_map,List.map_map]
  simp only [Function.comp_def,diagonalKeyCenter,realGiantSample,integerSample,Int.cast_natCast]

theorem reinsert_counterpart_cell_filter (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : SourceAssignment sources (Template.remainder j T)) :
    (Template.reinsert j T (assignedSlots sources (Template.extracted j T) u)
      (assignedSlots sources (Template.remainder j T) y)).filter
        (fun q => decide (q.role ≠ .compensation j ∧ q.role ≠ .bulk)) =
      (assignedSlots sources (Template.remainder j T) y).filter
        (fun q => decide (q.role ≠ .bulk)) := by
  have hf := (reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ y)).2
  have hff := congrArg (List.filter (fun q : SmallSlot => decide (q.role ≠ .bulk))) hf
  simp only [List.filter_filter] at hff
  have hepred : (fun a : SmallSlot => decide (a.role ≠ .bulk) && decide (a.role ≠ .compensation j)) =
      (fun a => decide (a.role ≠ .compensation j ∧ a.role ≠ .bulk)) := by
    funext a
    by_cases h₁ : a.role = .bulk <;> by_cases h₂ : a.role = .compensation j <;> simp [h₁,h₂]
  rw [hepred] at hff
  exact hff

end Ostmann.Arithmetic.HistoryGiantReferenceCounterpart

end

end OAI
