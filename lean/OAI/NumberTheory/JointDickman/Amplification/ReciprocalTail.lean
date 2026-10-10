import Mathlib.Analysis.PSeries
import OAI.NumberTheory.JointDickman.Probability.TwoSplitLaw

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

open Classical in
/-- The cell probability comparison has error at most `9/(8N)` when all
allowed primes exceed `N`. -/
theorem twoSplitPrimeProducts_cell_tail_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (A B : Set ℕ) :
    |(∑ x, if (actualSplitProducts Q x).1 ∈ A ∧ (actualSplitProducts Q x).2 ∈ B then
        sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) -
      (∑ y, if (independentSplitProducts Q y).1 ∈ A ∧ (independentSplitProducts Q y).2 ∈ B then
        bernoulliProductMass univ
          (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0)| ≤
      9 / (8 * N : ℝ) := by
  calc
    _ ≤ (9 / 8 : ℝ) * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 :=
      twoSplitPrimeProducts_cell_bound Q hQ A B
    _ ≤ (9 / 8 : ℝ) * (1 / N) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail Q hN hcut) (by norm_num)
    _ = _ := by ring

end JointDickman

end OAI
