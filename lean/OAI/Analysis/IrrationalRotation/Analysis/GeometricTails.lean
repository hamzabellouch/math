import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection.GeometricTails

theorem reciprocal_step {K : ℕ → ℝ} (hpos : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) (j : ℕ) :
    1 / K (j + 1) ≤ (1 / 2 : ℝ) * (1 / K j) := by
  calc
    1 / K (j + 1) ≤ 1 / (2 * K j) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) (hpos j)) (hdouble j)
    _ = (1 / 2 : ℝ) * (1 / K j) := by ring

theorem reciprocal_add_le {K : ℕ → ℝ} (hpos : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) (j n : ℕ) :
    1 / K (j + n) ≤ (1 / K j) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      1 / K (j + (n + 1)) ≤ (1 / 2 : ℝ) * (1 / K (j + n)) := by
        simpa only [Nat.add_assoc] using reciprocal_step hpos hdouble (j + n)
      _ ≤ (1 / 2 : ℝ) * ((1 / K j) * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / K j) * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem summable_reciprocal {K : ℕ → ℝ} (hpos : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) :
    Summable (fun j => 1 / K j) := by
  apply Summable.of_nonneg_of_le (fun j => le_of_lt (one_div_pos.mpr (hpos j)))
  · intro j
    simpa using reciprocal_add_le hpos hdouble 0 j
  · simpa using summable_geometric_two.mul_left (1 / K 0)

theorem tsum_reciprocal_add_le {K : ℕ → ℝ} (hpos : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + n)) ≤ 2 / K j := by
  have hs : Summable (fun n : ℕ => 1 / K (j + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).mpr
      (summable_reciprocal hpos hdouble)
  calc
    (∑' n : ℕ, 1 / K (j + n)) ≤
        ∑' n : ℕ, (1 / K j) * (1 / 2 : ℝ) ^ n :=
      hs.tsum_le_tsum (reciprocal_add_le hpos hdouble j)
        (summable_geometric_two.mul_left (1 / K j))
    _ = 2 / K j := by rw [tsum_mul_left, tsum_geometric_two]; ring

theorem tsum_reciprocal_tail_le {K : ℕ → ℝ} (hpos : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + 1 + n)) ≤ 2 / K (j + 1) :=
  tsum_reciprocal_add_le hpos hdouble (j + 1)

theorem summable_height_div {K H : ℕ → ℝ} (hK : ∀ j, 0 < K j)
    (hH : ∀ j, 0 ≤ H j)
    (hbound : ∀ j, H (j + 1) / K (j + 1) ≤ (1 / 2 : ℝ) ^ j) :
    Summable (fun j => H j / K j) := by
  apply (summable_nat_add_iff 1).mp
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg (hH (j + 1)) (hK (j + 1)).le)
    hbound summable_geometric_two

theorem summable_one_add_height_div {K H : ℕ → ℝ} (hK : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1)) (hH : ∀ j, 0 ≤ H j)
    (hbound : ∀ j, H (j + 1) / K (j + 1) ≤ (1 / 2 : ℝ) ^ j) :
    Summable (fun j => (1 + H j) / K j) := by
  simpa only [add_div] using
    (summable_reciprocal hK hdouble).add (summable_height_div hK hH hbound)

theorem tsum_height_div_tail_le {K H : ℕ → ℝ} (hK : ∀ j, 0 < K j)
    (hH : ∀ j, 0 ≤ H j)
    (hbound : ∀ j, H (j + 1) / K (j + 1) ≤ (1 / 2 : ℝ) ^ j) :
    (∑' j : ℕ, H (j + 1) / K (j + 1)) ≤ 2 := by
  have hs : Summable (fun j : ℕ => H (j + 1) / K (j + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_height_div hK hH hbound)
  calc
    (∑' j : ℕ, H (j + 1) / K (j + 1)) ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
      hs.tsum_le_tsum hbound summable_geometric_two
    _ = 2 := tsum_geometric_two

end InvariantProjection.GeometricTails

end OAI
