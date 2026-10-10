import OAI.Combinatorics.EditApproximation.Geometry.DomainCounts
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The actual finite labeled state type

Physical nodes are retained as depth/path pairs. In particular, repeated
empty intervals remain distinct entries of the seed and refinement tables.
-/

namespace EditApproximation

open Finset





theorem targetInterval_card_le (n : ℕ) :
    Fintype.card (TargetInterval n) ≤ (targetStates n).length := by
  exact (targetStates n).toFinset_card_le





abbrev LabeledEntry (M nx ny : ℕ) :=
  PhysicalNode M (intervalTreeDepth M nx) × TargetInterval ny

def entrySourceInterval {M nx ny : ℕ} (entry : LabeledEntry M nx ny) : TargetInterval nx :=
  sourceIntervalAt M nx entry.1.1.val entry.1.2

def entrySource {α : Type*} (M : ℕ) (source : List α) {ny : ℕ}
    (entry : LabeledEntry M source.length ny) : List α :=
  substring source (entrySourceInterval entry).lo (entrySourceInterval entry).hi

def entryTarget {α : Type*} (target : List α) {M nx : ℕ}
    (entry : LabeledEntry M nx target.length) : List α :=
  substring target entry.2.lo entry.2.hi

theorem physicalNode_card (M J : ℕ) :
    Fintype.card (PhysicalNode M J) =
      ∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d) := by
  rw [Fintype.card_sigma]
  rw [sum_fin_eq_sum_range]
  apply sum_congr rfl
  intro d hd
  rw [dite_eq_left (mem_range.mp hd)]

theorem labeledEntry_card_le (M nx ny : ℕ) :
    Fintype.card (LabeledEntry M nx ny) ≤ labeledStateCount M nx ny := by
  rw [Fintype.card_prod, physicalNode_card]
  exact Nat.mul_le_mul_left _ (targetInterval_card_le ny)

theorem computed_labeledEntry_card_le (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    Fintype.card (LabeledEntry (integerParameters N).M nx ny) ≤ 2 ^ (5 * inputHeight N) :=
  (labeledEntry_card_le _ _ _).trans (computed_labeledStateCount_le N nx ny hN hnx hny hell)

theorem entrySource_length_le {α : Type*} (M : ℕ) (source : List α) {ny : ℕ}
    (entry : LabeledEntry M source.length ny) : (entrySource M source entry).length ≤ source.length := by
  simp only [entrySource, substring, List.length_drop, List.length_take]
  exact (Nat.sub_le _ _).trans (min_le_right _ _)

theorem entryTarget_length_le {α : Type*} (target : List α) {M nx : ℕ}
    (entry : LabeledEntry M nx target.length) : (entryTarget target entry).length ≤ target.length := by
  simp only [entryTarget, substring, List.length_drop, List.length_take]
  exact (Nat.sub_le _ _).trans (min_le_right _ _)

end EditApproximation

end OAI
