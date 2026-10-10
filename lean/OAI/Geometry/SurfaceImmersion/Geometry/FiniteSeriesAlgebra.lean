import Mathlib

namespace OAI

/-! Reindexing the derivative series of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma shifted_derivative_sum (z : ℝ) (a b : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (z ^ (i + 1) • a i + z ^ i • b i)) =
      b 0 + (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • (a (i - 1) + b i)) +
        z ^ (n + 1) • a n := by
  induction n with
  | zero => simp [add_comm]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    simp only [Nat.add_sub_cancel, smul_add]
    abel

lemma weighted_sum_split_zero (z : ℝ) (a : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), z ^ i • a i) =
      a 0 + ∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • a i := by
  rw [← Finset.sum_range_add_sum_Ico (fun i => z ^ i • a i) (by omega : 1 ≤ n + 1)]
  simp

lemma weighted_sum_split_endpoints (z : ℝ) (a : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 2), z ^ i • a i) =
      a 0 + (∑ i ∈ Finset.Ico 1 (n + 1), z ^ i • a i) + z ^ (n + 1) • a (n + 1) := by
  rw [Finset.sum_range_succ, weighted_sum_split_zero]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
