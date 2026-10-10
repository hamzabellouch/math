import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingCounterpart

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Arithmetic Arithmetic.HistoryOccurrenceVariables

def diagonalCellKeys {l : ℕ} (h : History l) (j : ℕ) : List (Key h) :=
  Sum.inl true :: diagonalRoleKeys h
    (fun q => decide (q.role≠.compensation j ∧ q.role≠.bulk))

def diagonalKeyCenter {l : ℕ} (h : History l) (G : ℝ) (center : ℕ→ℝ) : Key h→ℝ
  | .inl _ => G
  | .inr (.inl i) => center (h.root.small.get i).origin
  | .inr (.inr i) => center (internalSlot h i).origin

def remainingCounterpart (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (giant : PrimeSource) (A B G : ℝ) (center : ℕ→ℝ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) : ℝ :=
  (Real.exp A/(remainingProduct sources (Template.remainder j T) giant x:ℝ)) *
    ((((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod:ℝ)/Real.exp B) *
    (smoothPartition (Real.log (x.1.val:ℝ)-G) *
      (((assignedSlots sources (Template.remainder j T) x.2).filter
        (fun q => decide (q.role≠.bulk))).map
          (fun q => smoothPartition (Real.log (q.value:ℝ)-center q.origin))).prod)

def diagonalRootCounterpart {l : ℕ} (h : History l) (j : ℕ) (A B G : ℝ)
    (center : ℕ→ℝ) (x : Key h→ℝ) : ℝ :=
  rootCounterpart A B (diagonalHKeys h j) (diagonalUKeys h j)
    (Finset.univ : Finset (Fin (diagonalCellKeys h j).length))
    (fun i => diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
    (diagonalCellKeys h j).get x

private theorem diagonalRoleKeys_cells {l : ℕ} (h : History l) (pred : SmallSlot→Bool)
    (G : ℝ) (center : ℕ→ℝ) :
    (diagonalRoleKeys h pred).map (fun i => giantCell (diagonalKeyCenter h G center i)
      (integerSample h i:ℝ)) =
    (h.root.small.filter pred).map (fun q => giantCell (center q.origin) (q.value:ℝ)) := by
  have he : (List.finRange h.root.small.length).map h.root.small.get=h.root.small := by
    simpa only [←List.ofFn_eq_map] using List.ofFn_get h.root.small
  conv_rhs => rw [←he]
  simp only [diagonalRoleKeys,List.filter_map,List.map_map]
  rfl

private theorem diagonalCellKeys_product {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : h.root=remainingState sources T j giant p u x v)
    (G : ℝ) (center : ℕ→ℝ) :
    ((diagonalCellKeys h j).map (fun i => giantCell (diagonalKeyCenter h G center i)
      (integerSample h i:ℝ))).prod =
    smoothPartition (Real.log (x.1.val:ℝ)-G) *
      (((assignedSlots sources (Template.remainder j T) x.2).filter
        (fun q => decide (q.role≠.bulk))).map
          (fun q => smoothPartition (Real.log (q.value:ℝ)-center q.origin))).prod := by
  simp only [diagonalCellKeys,List.map_cons,List.prod_cons,diagonalRoleKeys_cells]
  simp only [diagonalKeyCenter,integerSample,Int.cast_natCast]
  rw [hroot]
  have hf := (reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ x.2)).2
  have hff := congrArg (List.filter (fun q : SmallSlot => decide (q.role≠.bulk))) hf
  simp only [List.filter_filter] at hff
  have hepred : (fun a : SmallSlot => decide (a.role≠.bulk) && decide (a.role≠.compensation j))=
      (fun a => decide (a.role≠.compensation j ∧ a.role≠.bulk)) := by
    funext a
    by_cases h₁ : a.role=.bulk <;> by_cases h₂ : a.role=.compensation j <;> simp [h₁,h₂]
  rw [hepred] at hff
  change giantCell G (x.1.val:ℝ) *
    (((Template.reinsert j T _ _).filter _).map (fun q => giantCell (center q.origin) (q.value:ℝ))).prod=_
  rw [hff,giantCell_of_pos G (by exact_mod_cast (giant.prime _ x.1.property).pos)]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro q hq
  exact giantCell_of_pos _ (by exact_mod_cast
    (assignedSlots_prime sources (Template.remainder j T) x.2 q (List.mem_filter.mp hq).1).pos)

theorem diagonalRootCounterpart_integer_sample {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : h.root=remainingState sources T j giant p u x v)
    (A B G : ℝ) (center : ℕ→ℝ) :
    diagonalRootCounterpart h j A B G center (fun i => (integerSample h i:ℝ)) =
      remainingCounterpart sources T j giant A B G center u x := by
  unfold diagonalRootCounterpart rootCounterpart counterpartArchimedean
  rw [diagonalHKeys_product h sources T j giant p u x v hroot,
    diagonalUKeys_product h sources T j giant p u x v hroot]
  have he : (∏i : Fin (diagonalCellKeys h j).length,
      giantCell (diagonalKeyCenter h G center ((diagonalCellKeys h j).get i))
        (integerSample h ((diagonalCellKeys h j).get i):ℝ)) =
    ((diagonalCellKeys h j).map (fun i => giantCell (diagonalKeyCenter h G center i)
      (integerSample h i:ℝ))).prod := by
    rw [←List.prod_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map (diagonalCellKeys h j)
      (fun i => giantCell (diagonalKeyCenter h G center i) (integerSample h i:ℝ))
  rw [he,diagonalCellKeys_product h sources T j giant p u x v hroot G center]
  rfl

end Ostmann.Construction

end

end OAI
