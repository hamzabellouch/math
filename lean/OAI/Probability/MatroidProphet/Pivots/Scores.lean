import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

lemma sum_positive_iff_pivot_positive (s : Finset α) (w : α → ℝ) {p : α}
    (hp : p ∈ s) (hdom : ∑ i ∈ s.erase p, |w i| < |w p|) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  have habs : |∑ i ∈ s.erase p, w i| ≤ ∑ i ∈ s.erase p, |w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbounds := abs_le.mp habs
  have hsum : (∑ i ∈ s, w i) = (∑ i ∈ s.erase p, w i) + w p :=
    (Finset.sum_erase_add _ _ hp).symm
  rw [hsum]
  by_cases hwp : 0 ≤ w p
  · rw [abs_of_nonneg hwp] at hdom
    constructor <;> intro h <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hwp)] at hdom
    constructor <;> intro h <;> linarith

lemma sum_negative_iff_pivot_negative (s : Finset α) (w : α → ℝ) {p : α}
    (hp : p ∈ s) (hdom : ∑ i ∈ s.erase p, |w i| < |w p|) :
    (∑ i ∈ s, w i) < 0 ↔ w p < 0 := by
  have h := sum_positive_iff_pivot_positive s (fun i => -w i) hp (by simpa using hdom)
  simpa only [Finset.sum_neg_distrib, neg_pos] using h

lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sum_two_pow_lt (s : Finset ℕ) (k : ℕ) (hsk : ∀ i ∈ s, i < k) :
    (∑ i ∈ s, (2 : ℝ)^i) < 2^k := by
  have hsub : s ⊆ Finset.range k := fun i hi => Finset.mem_range.mpr (hsk i hi)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => show 0 ≤ (2 : ℝ)^i from pow_nonneg (by norm_num) _)
  rw [sum_range_two_pow] at hle
  linarith

lemma sum_signed_powers_positive_iff (s : Finset ℕ) (w : ℕ → ℝ) {p : ℕ}
    (hp : p ∈ s) (hmax : ∀ i ∈ s, i ≤ p) (hw : ∀ i ∈ s, |w i| = 2^i) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  apply sum_positive_iff_pivot_positive s w hp
  rw [hw p hp]
  calc
    (∑ i ∈ s.erase p, |w i|) = ∑ i ∈ s.erase p, (2 : ℝ)^i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hw i (Finset.mem_of_mem_erase hi)
    _ < 2^p := sum_two_pow_lt _ _ (fun i hi =>
      lt_of_le_of_ne (hmax i (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi))

lemma sum_positive_iff_max_exponent (s : Finset α) (w : α → ℝ) (exponent : α → ℕ)
    (hinj : Function.Injective exponent) {p : α} (hp : p ∈ s)
    (hmax : ∀ i ∈ s, i ≠ p → exponent i < exponent p)
    (hw : ∀ i ∈ s, |w i| = 2 ^ exponent i) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  apply sum_positive_iff_pivot_positive s w hp
  rw [hw p hp]
  calc
    (∑ i ∈ s.erase p, |w i|) = ∑ i ∈ s.erase p, (2 : ℝ) ^ exponent i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hw i (Finset.mem_of_mem_erase hi)
    _ = ∑ j ∈ (s.erase p).image exponent, (2 : ℝ) ^ j := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact hinj hij
    _ < 2 ^ exponent p := by
      apply sum_two_pow_lt
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

end Pivots
end MatroidProphet

end OAI
