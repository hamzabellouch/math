import OAI.Analysis.LipschitzHilbert.Trees.HierarchyVariation

namespace OAI

/-! The cancellation of boundary losses along an eligible path in §11. -/

open scoped BigOperators

namespace LipschitzHilbert

/-- Shifting a finite difference sum leaves only its two boundary blocks. -/
theorem sum_range_shift_difference (a : ℕ → ℝ) (k r : ℕ) :
    (∑ i ∈ Finset.range k, (a i - a (i + r))) =
      (∑ i ∈ Finset.range r, a i) - ∑ i ∈ Finset.range r, a (i + k) := by
  have hkr := Finset.sum_range_add a k r
  have hrk := Finset.sum_range_add a r k
  have hlen : (∑ i ∈ Finset.range (k + r), a i) =
      ∑ i ∈ Finset.range (r + k), a i := by rw [Nat.add_comm k r]
  have hs1 : (∑ i ∈ Finset.range k, a (i + r)) =
      ∑ i ∈ Finset.range k, a (r + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i r]
  have hs2 : (∑ i ∈ Finset.range r, a (i + k)) =
      ∑ i ∈ Finset.range r, a (k + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i k]
  rw [Finset.sum_sub_distrib, hs1, hs2]
  linarith

/-- The number of path levels does not enter the boundary-loss estimate.
Here `r` is the shift coming from the ratio of two angular radii. -/
theorem boundary_loss_sum_le (a loss : ℕ → ℝ) (k r : ℕ) {B : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hbound : ∀ i < r, a i ≤ B)
    (hloss : ∀ i < k, loss i ≤ a i - a (i + r)) :
    (∑ i ∈ Finset.range k, loss i) ≤ (r : ℝ) * B := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, (a i - a (i + r)) :=
      Finset.sum_le_sum fun i hi => hloss i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range r, a i) - ∑ i ∈ Finset.range r, a (i + k) :=
      sum_range_shift_difference a k r
    _ ≤ ∑ i ∈ Finset.range r, a i :=
      sub_le_self _ (Finset.sum_nonneg fun i _ => ha (i + k))
    _ ≤ ∑ _i ∈ Finset.range r, B :=
      Finset.sum_le_sum fun i hi => hbound i (Finset.mem_range.mp hi)
    _ = (r : ℝ) * B := by simp

end LipschitzHilbert

end OAI
