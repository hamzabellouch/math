import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ParameterTails

theorem half_decay_iterate {a : ℕ → ℝ}
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j n : ℕ) :
    a (j + n) ≤ a j * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a (j + (n + 1)) ≤ a (j + n) / 2 := by
          simpa only [Nat.add_assoc] using hstep (j + n)
        _ ≤ (a j * (1 / 2 : ℝ) ^ n) / 2 := by linarith
        _ = a j * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem summable_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) : Summable a := by
  apply Summable.of_nonneg_of_le ha
    (fun n => by simpa using half_decay_iterate hstep 0 n)
  simpa using summable_geometric_two.mul_left (a 0)

theorem tsum_tail_le_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j : ℕ) :
    (∑' n : ℕ, a (j + n)) ≤ 2 * a j := by
  have hs : Summable (fun n : ℕ => a (j + n)) :=
    summable_of_half_decay (fun n => ha (j + n))
      (fun n => by simpa only [Nat.add_assoc] using hstep (j + n))
  calc
    (∑' n : ℕ, a (j + n)) ≤ ∑' n : ℕ, a j * (1 / 2 : ℝ) ^ n :=
      hs.tsum_le_tsum (half_decay_iterate hstep j)
        (summable_geometric_two.mul_left (a j))
    _ = 2 * a j := by rw [tsum_mul_left, tsum_geometric_two]; ring

theorem reciprocal_half_decay {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (n : ℕ) :
    1 / K (n + 1) ≤ (1 / K n) / 2 := by
  calc
    1 / K (n + 1) ≤ 1 / (2 * K n) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) (hK n)) (hdouble n)
    _ = (1 / K n) / 2 := by ring

theorem reciprocal_tail_bound {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + 1 + n)) ≤ 2 / K (j + 1) := by
  simpa only [div_eq_mul_inv, one_mul] using
    tsum_tail_le_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
      (reciprocal_half_decay hK hdouble) (j + 1)

theorem summable_reciprocal {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) :
    Summable (fun n => 1 / K n) :=
  summable_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
    (reciprocal_half_decay hK hdouble)

theorem summable_partition_cost {K h : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (hh : ∀ n, 0 ≤ h n)
    (hheight : ∀ n, h (n + 1) / K (n + 1) ≤ (1 / 2 : ℝ) ^ n) :
    Summable (fun n => (1 + h n) / K n) := by
  have hsum : Summable (fun n => h n / K n) := by
    apply (summable_nat_add_iff 1).mp
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg (hh (n + 1)) (hK (n + 1)).le)
      hheight summable_geometric_two
  simpa only [add_div] using (summable_reciprocal hK hdouble).add hsum

end Invariant233.ParameterTails

end OAI
