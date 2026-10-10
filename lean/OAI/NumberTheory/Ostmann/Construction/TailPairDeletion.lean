import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeCoverageWeight

namespace OAI

/-! # Cost of removing small endpoints from a nonnegative pair sum -/
namespace Ostmann
open scoped Classical BigOperators

 theorem pair_sum_filter_error (A B : Finset ℕ) (lo : ℕ) (W : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hW : ∀ a ∈ A, ∀ b ∈ B, W (a + b) ≤ M) :
    (∑ a ∈ A, ∑ b ∈ B, W (a + b)) ≤
      (∑ a ∈ A.filter (fun a => lo < a), ∑ b ∈ B.filter (fun b => lo < b), W (a + b)) +
      M * (((A.filter (fun a => a ≤ lo)).card : ℝ) * B.card +
        (A.card : ℝ) * (B.filter (fun b => b ≤ lo)).card) := by
  have hp (a) (ha : a ∈ A) (b) (hb : b ∈ B) :
      W (a + b) ≤ (if lo < a then if lo < b then W (a + b) else 0 else 0) +
        (if a ≤ lo then M else 0) + (if b ≤ lo then M else 0) := by
    by_cases hla : lo < a <;> by_cases hlb : lo < b
    · simp only [hla, hlb, ite_true, Nat.not_le.mpr hla, Nat.not_le.mpr hlb, ite_false, add_zero]
      exact le_rfl
    · simp only [hla, hlb, ite_true, ite_false, Nat.not_le.mpr hla,
        Nat.le_of_not_lt hlb, zero_add]
      exact hW a ha b hb
    · simp only [hla, hlb, ite_true, ite_false, Nat.le_of_not_lt hla,
        Nat.not_le.mpr hlb, zero_add, add_zero]
      exact hW a ha b hb
    · simp only [hla, hlb, ite_true, ite_false, Nat.le_of_not_lt hla,
        Nat.le_of_not_lt hlb, zero_add]
      exact (hW a ha b hb).trans (by linarith)
  have hh := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hp a ha b hb))
  have hg : (∑ a ∈ A, ∑ b ∈ B,
      if lo < a then if lo < b then W (a + b) else 0 else 0) =
      ∑ a ∈ A.filter (fun a => lo < a), ∑ b ∈ B.filter (fun b => lo < b), W (a + b) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
  have hA : (∑ a ∈ A, ∑ _b ∈ B, if a ≤ lo then M else 0) =
      ((A.filter (fun a => a ≤ lo)).card : ℝ) * B.card * M := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [← Finset.sum_filter]
    simp
    ring
  have hB : (∑ _a ∈ A, ∑ b ∈ B, if b ≤ lo then M else 0) =
      (A.card : ℝ) * (B.filter (fun b => b ≤ lo)).card * M := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  simp only [Finset.sum_add_distrib] at hh
  rw [hg, hA, hB] at hh
  convert hh using 1
  ring

 theorem prefix_pair_sum_le_tail (A B : Set ℕ) (lo X : ℕ) (hlo : lo ≤ X)
    (W : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hW : ∀ n, W n ≤ M) :
    (∑ a ∈ summandPrefix A X, ∑ b ∈ summandPrefix B X, W (a + b)) ≤
      (∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W (a + b)) +
      M * (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
        ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card) := by
  have ht (T : Set ℕ) : (summandPrefix T X).filter (fun a => lo < a) = summandTail T lo X := by
    ext a
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    tauto
  have hs (T : Set ℕ) : (summandPrefix T X).filter (fun a => a ≤ lo) = summandPrefix T lo := by
    ext a
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hh⟩; exact ⟨ha, hh⟩
    · rintro ⟨ha, hh⟩; exact ⟨⟨ha, hh.trans hlo⟩, hh⟩
  simpa only [ht, hs] using pair_sum_filter_error (summandPrefix A X) (summandPrefix B X)
    lo W M hM (fun a _ b _ => hW (a + b))

end Ostmann

end OAI
