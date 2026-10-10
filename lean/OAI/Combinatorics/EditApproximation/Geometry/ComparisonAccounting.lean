import OAI.Combinatorics.EditApproximation.Geometry.TreeAccounting

namespace OAI

/-!
# Accuracy accounting on the comparison tree

The clipped regrets cancel across every physical frontier. Terminal nodes
can be carried forward in one child slot, with zero in the others, as in
the complete-tree representation used for the curvature accounting.
-/

namespace EditApproximation

open Finset

theorem tree_regret_telescope (M J : ℕ)
    (value charge : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d,
      (value d node - charge d node -
        ∑ child : Fin M, value (d + 1) (node, child))) =
      value 0 PUnit.unit - (∑ node : TreeLayer M J, value J node) -
        ∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node := by
  have hpoint d (node : TreeLayer M d) :
      value d node - charge d node - (∑ child : Fin M, value (d + 1) (node, child)) =
        (value d node - ∑ child : Fin M, value (d + 1) (node, child)) - charge d node := by ring
  simp_rw [hpoint, sum_sub_distrib]
  have htelescope := tree_frontier_telescope M J value
  simp only [sum_sub_distrib] at htelescope
  rw [htelescope]

theorem tree_regret_time_bound (M J S : ℕ)
    (value : ℕ → (d : ℕ) → TreeLayer M d → ℝ)
    (charge : (d : ℕ) → TreeLayer M d → ℝ) (terminalBound : ℝ)
    (hmonotone : ∀ t < S, value S 0 PUnit.unit ≤ value (t + 1) 0 PUnit.unit)
    (hterminal : ∀ t < S, (∑ node : TreeLayer M J, value (t + 1) J node) ≤ terminalBound) :
    (S : ℝ) * value S 0 PUnit.unit ≤
      (S : ℝ) * (terminalBound + ∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node) +
        ∑ t ∈ range S, ∑ d ∈ range J, ∑ node : TreeLayer M d,
          (value (t + 1) d node - charge d node -
            ∑ child : Fin M, value (t + 1) (d + 1) (node, child)) := by
  have hpoint (t : ℕ) (ht : t ∈ range S) : value S 0 PUnit.unit ≤
      terminalBound + (∑ d ∈ range J, ∑ node : TreeLayer M d, charge d node) +
        ∑ d ∈ range J, ∑ node : TreeLayer M d,
          (value (t + 1) d node - charge d node -
            ∑ child : Fin M, value (t + 1) (d + 1) (node, child)) := by
    rw [tree_regret_telescope]
    linarith [hmonotone t (mem_range.mp ht), hterminal t (mem_range.mp ht)]
  have hsum := sum_le_sum hpoint
  simpa only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_add] using hsum

/-- Dividing the time telescope yields the positive-excess estimate.
For clipped root values, `root-D` is exactly the positive part of error. -/
theorem root_excess_from_time_bound {S root D terminal charge regret error : ℝ}
    (hS : 0 < S)
    (htime : S * root ≤ S * (terminal + charge) + regret)
    (hterminal : terminal + charge ≤ D + error * D)
    (hregret : regret ≤ S * error * D) :
    root - D ≤ 2 * error * D := by
  have hmain := mul_le_mul_of_nonneg_left hterminal hS.le
  have hbound : S * (root - D) ≤ S * (2 * error * D) := by nlinarith
  exact (mul_le_mul_iff_right₀ hS).mp hbound

end EditApproximation

end OAI
