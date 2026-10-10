import OAI.Combinatorics.EditApproximation.Geometry.BalancedIntervals

namespace OAI

/-! Actual prefix lengths of the labeled balanced source partition. -/

namespace EditApproximation

theorem sourceChildrenList_eq_balancedPieces {α : Type*} (source : List α)
    {M : ℕ} (parent : TargetInterval source.length) :
    (List.ofFn fun i : Fin M =>
      substring source (sourceChild parent i).lo (sourceChild parent i).hi) =
        balancedPieces source parent.lo (parent.hi - parent.lo) M := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, balancedPieces_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, balancedPieces, List.getElem_map, List.getElem_range, sourceChild]

theorem sourceChildren_prefix_length {α : Type*} (source : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length) (j : ℕ) (hj : j ≤ M) :
    ((List.ofFn fun i : Fin M =>
      substring source (sourceChild parent i).lo (sourceChild parent i).hi).take j).flatten.length =
        balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo := by
  rw [sourceChildrenList_eq_balancedPieces]
  simp only [balancedPieces, ← List.map_take, List.take_range, Nat.min_eq_left hj]
  rw [balancedPieces_prefix]
  have hcut : balancedCut parent.lo (parent.hi - parent.lo) M j ≤ source.length := by
    have h := (balancedCut_bounds parent.lo (parent.hi - parent.lo) M j hM hj).2
    rw [Nat.add_sub_of_le parent.ordered] at h
    exact h.trans parent.valid
  simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left hcut]

end EditApproximation

end OAI
