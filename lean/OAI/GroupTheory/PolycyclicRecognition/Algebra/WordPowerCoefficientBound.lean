import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordMinimumDegree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordCutCounting
import Mathlib.Tactic.NormNum

namespace OAI

/-! # Binomial bounds for powers of a word series with zero constant term -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n : ℕ}

theorem word_power_coefficient_bound (p : RationalWords n) (hp : p.coeff 1 = 0)
    (hbound : ∀ w, |p.coeff w| ≤ 1) (k : ℕ) (w : FreeMonoid (Fin n)) (hw : 0 < w.length) :
    |(p ^ (k + 1)).coeff w| ≤ ((w.length - 1).choose k : ℚ) := by
  induction k generalizing w with
  | zero => simpa only [zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one] using hbound w
  | succ k ih =>
    rw [pow_succ p (k + 1), word_coeff_mul]
    have hterm (i : Fin (w.length + 1)) :
        |(p ^ (k + 1)).coeff (wordSplit w i).1 * p.coeff (wordSplit w i).2| ≤
          if 0 < i.val ∧ i.val < w.length then ((i.val - 1).choose k : ℚ) else 0 := by
      have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
        rw [← FreeMonoid.length_mul, wordSplit_mul]
      rw [wordSplit_left_length] at hlen
      by_cases hi0 : i.val = 0
      · have hz : (p ^ (k + 1)).coeff (wordSplit w i).1 = 0 :=
          wordMinimumDegree_pow hp (k + 1) _ (by rw [wordSplit_left_length, hi0]; omega)
        simp [hi0, hz]
      · by_cases hiw : i.val = w.length
        · have hz : (wordSplit w i).2 = 1 :=
            FreeMonoid.length_eq_zero.mp (by omega)
          simp [hiw, hz, hp]
        · have hi : 0 < i.val ∧ i.val < w.length := by omega
          rw [ite_eq_left hi, abs_mul]
          have hb := ih (wordSplit w i).1 (by rw [wordSplit_left_length]; exact hi.1)
          rw [wordSplit_left_length] at hb
          exact (mul_le_mul hb (hbound _) (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)
    calc
      _ ≤ ∑ i : Fin (w.length + 1),
          |(p ^ (k + 1)).coeff (wordSplit w i).1 * p.coeff (wordSplit w i).2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (w.length + 1),
          if 0 < i.val ∧ i.val < w.length then ((i.val - 1).choose k : ℚ) else 0 :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((w.length - 1).choose (k + 1) : ℚ) := by
        exact_mod_cast sum_internal_word_cuts w.length k hw

end PolycyclicRecognition

end

end OAI
