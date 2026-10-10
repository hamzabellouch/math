import OAI.Combinatorics.EditApproximation.Geometry.TreeParameters

namespace OAI

/-!
# Summing width-sensitive work over physical levels

At depth `d`, the product of the number of nodes and their maximum
balanced width is at most the source length plus one layer's node count.
This is the precise summation used for fresh coarse-entry requests.
-/

namespace EditApproximation

open Finset

theorem mul_ceilDiv_le_add (n m : ℕ) (hm : 0 < m) :
    m * (n ⌈/⌉ m) ≤ n + m := by
  have hceil : n ⌈/⌉ m ≤ n / m + 1 :=
    (ceilDiv_le_iff_le_mul hm).2 (Nat.lt_mul_div_succ n hm).le
  have hmul := Nat.mul_le_mul_left m hceil
  have hfloor := Nat.mul_div_le n m
  nlinarith

theorem layer_width_work (M n d : ℕ) (hM : 0 < M) :
    M ^ d * (1 + n ⌈/⌉ M ^ d) ≤ n + 2 * M ^ d := by
  have hwidth := mul_ceilDiv_le_add n (M ^ d) (pow_pos hM d)
  nlinarith

theorem interval_tree_width_work (M n : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (intervalTreeDepth M n + 1), M ^ d * (1 + n ⌈/⌉ M ^ d)) ≤
      (intervalTreeDepth M n + 1) * n + 4 * M * max 1 n := by
  have hpoint (d : ℕ) (_ : d ∈ range (intervalTreeDepth M n + 1)) :=
    layer_width_work M n d (by omega)
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at hsum
  have hnodes := complete_tree_node_count M (intervalTreeDepth M n) hM
  simp_rw [treeLayer_card] at hnodes
  have hcapacity := intervalTreeDepth_power_le M n hM
  nlinarith

end EditApproximation

end OAI
