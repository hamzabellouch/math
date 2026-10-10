import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # Binomial counting of the internal cuts of a word -/

namespace PolycyclicRecognition

open scoped BigOperators

theorem sum_range_prefix_choose (d k : ℕ) :
    (∑ i ∈ Finset.range d, i.choose k) = d.choose (k + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    exact Nat.add_comm _ _

theorem sum_internal_word_cuts (d k : ℕ) (hd : 0 < d) :
    (∑ i : Fin (d + 1), if 0 < i.val ∧ i.val < d then (i.val - 1).choose k else 0) =
      (d - 1).choose (k + 1) := by
  cases d with
  | zero => omega
  | succ d =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, lt_self_iff_false, false_and, ite_false, zero_add,
      Fin.val_succ, Nat.add_sub_cancel]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.zero_lt_succ,
      Nat.add_lt_add_iff_right, true_and, lt_self_iff_false, ite_false, add_zero]
    simpa only [Fin.isLt, ite_true, ← Fin.sum_univ_eq_sum_range] using sum_range_prefix_choose d k

end PolycyclicRecognition

end OAI
