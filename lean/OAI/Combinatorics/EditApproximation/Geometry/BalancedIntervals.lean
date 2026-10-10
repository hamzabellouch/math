import OAI.Combinatorics.EditApproximation.Coarse.CoarseSeed
import OAI.Combinatorics.EditApproximation.Geometry.TreeAccounting
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The actual balanced interval cuts

The fixed interval tree uses cuts `l + floor(i*width/M)`. Their substring
pieces concatenate exactly to the parent, including repeated cuts and
empty pieces. These facts instantiate optimal alignment splitting on the
manuscript's actual source intervals.
-/

namespace EditApproximation



theorem balancedCut_zero (lo width M : ℕ) : balancedCut lo width M 0 = lo := by
  simp [balancedCut]

theorem balancedCut_last (lo width M : ℕ) (hM : 0 < M) :
    balancedCut lo width M M = lo + width := by
  simp only [balancedCut, Nat.mul_div_cancel_left _ hM]

theorem balancedCut_monotone (lo width M : ℕ) : Monotone (balancedCut lo width M) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right width hij)) lo

theorem balancedCut_bounds (lo width M i : ℕ) (hM : 0 < M) (hi : i ≤ M) :
    lo ≤ balancedCut lo width M i ∧ balancedCut lo width M i ≤ lo + width := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [← balancedCut_last lo width M hM]
    exact balancedCut_monotone lo width M hi

def balancedPieces {α : Type*} (word : List α) (lo width M : ℕ) : List (List α) :=
  (List.range M).map fun i => substring word (balancedCut lo width M i) (balancedCut lo width M (i + 1))

theorem balancedPieces_prefix {α : Type*} (word : List α) (lo width M j : ℕ) :
    ((List.range j).map fun i =>
      substring word (balancedCut lo width M i) (balancedCut lo width M (i + 1))).flatten =
        substring word lo (balancedCut lo width M j) := by
  induction j with
  | zero => simp [balancedCut, substring]
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    exact (substring_split word lo (balancedCut lo width M j) (balancedCut lo width M (j + 1))
      (Nat.le_add_right _ _) (balancedCut_monotone lo width M (Nat.le_succ j))).symm

theorem balancedPieces_flatten {α : Type*} (word : List α) (lo width M : ℕ) (hM : 0 < M) :
    (balancedPieces word lo width M).flatten = substring word lo (lo + width) := by
  rw [balancedPieces, balancedPieces_prefix, balancedCut_last lo width M hM]

theorem balancedPieces_length {α : Type*} (word : List α) (lo width M : ℕ) :
    (balancedPieces word lo width M).length = M := by
  simp only [balancedPieces, List.length_map, List.length_range]





theorem sourceChild_partition {α : Type*} (word : List α) {M : ℕ} (hM : 0 < M)
    (parent : TargetInterval word.length) :
    (List.ofFn fun child : Fin M =>
      substring word (sourceChild parent child).lo (sourceChild parent child).hi).flatten =
        substring word parent.lo parent.hi := by
  have hlist : (List.ofFn fun child : Fin M =>
      substring word (sourceChild parent child).lo (sourceChild parent child).hi) =
      balancedPieces word parent.lo (parent.hi - parent.lo) M := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, balancedPieces_length]
    · intro i hi hj
      simp only [List.getElem_ofFn, balancedPieces, List.getElem_map, List.getElem_range, sourceChild]
  rw [hlist, balancedPieces_flatten word parent.lo (parent.hi - parent.lo) M hM,
    Nat.add_sub_of_le parent.ordered]

end EditApproximation

end OAI
