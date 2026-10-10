import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

open Finset

namespace PiExponent

theorem sum_range_two_pow_eq_dyadic (f : ℕ → ℝ) (k : ℕ) :
    ∑ q ∈ range (2 ^ k), f q =
      f 0 + ∑ j ∈ range k, ∑ q ∈ Ico (2 ^ j) (2 ^ (j + 1)), f q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 ^ k ≤ 2 ^ (k + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    rw [← sum_range_add_sum_Ico f hk, ih, sum_range_succ]
    rw [add_assoc]

theorem summable_of_dyadic_norm_blocks {f g : ℕ → ℝ}
    (hg : Summable g)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ ≤ g k) :
    Summable f := by
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    (sum_nonneg fun _ _ => norm_nonneg _).trans (hblock k)
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun _ => norm_nonneg _) (c := ‖f 0‖ + ∑' k, g k)
  intro n
  calc
    ∑ q ∈ range n, ‖f q‖ ≤ ∑ q ∈ range (2 ^ n), ‖f q‖ :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_of_lt n.lt_two_pow_self))
        (fun _ _ _ => norm_nonneg _)
    _ = ‖f 0‖ + ∑ k ∈ range n, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ :=
      sum_range_two_pow_eq_dyadic _ _
    _ ≤ ‖f 0‖ + ∑ k ∈ range n, g k :=
      add_le_add le_rfl (sum_le_sum fun k _ => hblock k)
    _ ≤ ‖f 0‖ + ∑' k, g k :=
      add_le_add le_rfl (hg.sum_le_tsum (range n) (fun k _ => hg0 k))

theorem summable_of_dyadic_blocks {f g : ℕ → ℝ}
    (hf : ∀ q, 0 < q → 0 ≤ f q) (hg : Summable g)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q ≤ g k) :
    Summable f := by
  apply summable_of_dyadic_norm_blocks hg
  intro k
  calc
    ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ =
        ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q := by
      apply sum_congr rfl
      intro q hq
      exact Real.norm_of_nonneg (hf q ((pow_pos (by decide) k).trans_le (mem_Ico.mp hq).1))
    _ ≤ g k := hblock k

theorem summable_of_dyadic_geometric {f : ℕ → ℝ} {M r : ℝ}
    (hf : ∀ q, 0 < q → 0 ≤ f q) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q ≤ M * r ^ k) :
    Summable f :=
  summable_of_dyadic_blocks hf ((summable_geometric_of_lt_one hr0 hr1).mul_left M) hblock

end PiExponent

end OAI
