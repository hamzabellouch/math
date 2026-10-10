import OAI.Combinatorics.EditApproximation.Geometry.BalancedIntervals

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem ceilDiv_comp (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a * b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb), Nat.mul_assoc]

theorem balanced_child_width_le_ceiling (width M i : ℕ) (hM : 0 < M) :
    ((i + 1) * width / M) - i * width / M ≤ width ⌈/⌉ M := by
  let c := width ⌈/⌉ M
  have hceil : width ≤ M * c := (ceilDiv_le_iff_le_mul hM).mp (le_refl c)
  have hfloor := Nat.lt_mul_div_succ (i * width) hM
  have hsum : i * width + width < (i * width / M + c + 1) * M := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul hM).2 hsum
  have hid : (i + 1) * width = i * width + width := by ring
  rw [hid]
  omega

theorem sourceChild_width_le_ceiling {n M : ℕ} (parent : TargetInterval n) (child : Fin M) :
    (sourceChild parent child).hi - (sourceChild parent child).lo ≤
      (parent.hi - parent.lo) ⌈/⌉ M := by
  dsimp only [sourceChild, balancedCut]
  rw [Nat.add_sub_add_left]
  exact balanced_child_width_le_ceiling _ _ _ (Nat.zero_lt_of_lt child.isLt)

theorem sourceIntervalAt_width (M n d : ℕ) (hM : 0 < M) (node : TreeLayer M d) :
    (sourceIntervalAt M n d node).hi - (sourceIntervalAt M n d node).lo ≤ n ⌈/⌉ M ^ d := by
  induction d with
  | zero => simp [sourceIntervalAt]
  | succ d ih =>
    have hchild := sourceChild_width_le_ceiling (sourceIntervalAt M n d node.1) node.2
    have hmono := (gc_mul_ceilDiv hM).monotone_l (ih node.1)
    have hcomp := ceilDiv_comp n (M ^ d) M (pow_pos hM d) hM
    change (sourceChild (sourceIntervalAt M n d node.1) node.2).hi -
        (sourceChild (sourceIntervalAt M n d node.1) node.2).lo ≤ n ⌈/⌉ M ^ (d + 1)
    exact hchild.trans (hmono.trans_eq (by rw [hcomp, pow_succ]))

theorem sourceIntervalAt_leaf_width (M n J : ℕ) (hM : 0 < M) (hcapacity : n ≤ M ^ J)
    (node : TreeLayer M J) :
    (sourceIntervalAt M n J node).hi - (sourceIntervalAt M n J node).lo ≤ 1 := by
  apply (sourceIntervalAt_width M n J hM node).trans
  apply (ceilDiv_le_iff_le_mul (pow_pos hM J)).2
  simpa only [Nat.mul_one] using hcapacity

theorem treeLayer_card (M d : ℕ) : Fintype.card (TreeLayer M d) = M ^ d := by
  induction d with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | succ d ih =>
    change Fintype.card (TreeLayer M d × Fin M) = M ^ (d + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

theorem complete_tree_node_count (M J : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d)) ≤ 2 * M ^ J := by
  simp_rw [treeLayer_card]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, pow_succ]
    have hmul := Nat.mul_le_mul_right (M ^ J) hM
    nlinarith

end EditApproximation

end OAI
