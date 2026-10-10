import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem affine_witness_count_le_exp (q m : ℕ) (hq : 1 ≤ q) :
    ((q * (q + 1)).choose m : ℝ) ≤ (q : ℝ) ^ m * Real.exp (2 * q) := by
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp : ((q : ℝ) + 1) ^ m / (m.factorial : ℝ) ≤
      Real.exp (2 * q) :=
    (Real.pow_div_factorial_le_exp ((q : ℝ) + 1) (by positivity) m).trans
      (Real.exp_le_exp.mpr (by linarith))
  calc
    ((q * (q + 1)).choose m : ℝ)
        ≤ ((q * (q + 1) : ℕ) : ℝ) ^ m / (m.factorial : ℝ) :=
      Nat.choose_le_pow_div m (q * (q + 1))
    _ = (q : ℝ) ^ m * (((q : ℝ) + 1) ^ m / (m.factorial : ℝ)) := by
      push_cast
      rw [mul_pow, mul_div_assoc]
    _ ≤ (q : ℝ) ^ m * Real.exp (2 * q) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

theorem sum_choose_div_pow_le_exp (n M : ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ m ∈ Finset.range M, (n.choose m : ℝ) / r ^ m) ≤ Real.exp (n / r) := by
  calc
    (∑ m ∈ Finset.range M, (n.choose m : ℝ) / r ^ m)
        ≤ ∑ m ∈ Finset.range M, (n / r) ^ m / (m.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        (n.choose m : ℝ) / r ^ m
            ≤ ((n : ℝ) ^ m / (m.factorial : ℝ)) / r ^ m :=
          div_le_div_of_nonneg_right (Nat.choose_le_pow_div m n) (by positivity)
        _ = (n / r) ^ m / (m.factorial : ℝ) := by
          rw [div_pow]
          ring
    _ ≤ Real.exp (n / r) := Real.sum_le_exp_of_nonneg (by positivity) M

theorem affine_weighted_witness_sum_le_exp (q : ℕ) (hq : 1 ≤ q) :
    (∑ m ∈ Finset.range (q + 1),
      ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) ≤ Real.exp (2 * q) := by
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  calc
    (∑ m ∈ Finset.range (q + 1),
        ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m)
        ≤ Real.exp (((q * (q + 1) : ℕ) : ℝ) / q) :=
      sum_choose_div_pow_le_exp (q * (q + 1)) (q + 1) hqpos
    _ = Real.exp ((q : ℝ) + 1) := by
      congr 1
      push_cast
      field_simp
    _ ≤ Real.exp (2 * q) := Real.exp_le_exp.mpr (by linarith)

theorem affine_witness_union_bound (q : ℕ) (hq : 1 ≤ q)
    (p : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hp : ∀ m ≤ q, p m ≤ A / (q : ℝ) ^ m) :
    (∑ m ∈ Finset.range (q + 1), ((q * (q + 1)).choose m : ℝ) * p m) ≤
      A * Real.exp (2 * q) := by
  calc
    (∑ m ∈ Finset.range (q + 1), ((q * (q + 1)).choose m : ℝ) * p m)
        ≤ ∑ m ∈ Finset.range (q + 1),
          A * (((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
      calc
        ((q * (q + 1)).choose m : ℝ) * p m
            ≤ ((q * (q + 1)).choose m : ℝ) * (A / (q : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left (hp m hmle) (by positivity)
        _ = A * (((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by ring
    _ = A * (∑ m ∈ Finset.range (q + 1),
        ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by
      rw [Finset.mul_sum]
    _ ≤ A * Real.exp (2 * q) :=
      mul_le_mul_of_nonneg_left (affine_weighted_witness_sum_le_exp q hq) hA

end Balanced

end OAI
