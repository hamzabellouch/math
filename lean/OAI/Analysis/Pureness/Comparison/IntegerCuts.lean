import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace OAI
open scoped BigOperators

namespace CuntzComparison

noncomputable def integerCutCount (L : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, if (j + 1 : ℕ) < s then 1 else 0

lemma integerCutCount_succ (L : ℕ) (s : ℝ) :
    integerCutCount (L + 1) s = integerCutCount L s +
      if (L + 1 : ℕ) < s then 1 else 0 := by
  simp only [integerCutCount, Finset.sum_range_succ]

lemma integerCutCount_above (L : ℕ) {s : ℝ} (hs : (L : ℝ) < s) :
    integerCutCount L s = L := by
  unfold integerCutCount
  have h : ∀ j ∈ Finset.range L, (if (j + 1 : ℕ) < s then (1 : ℝ) else 0) = 1 := by
    intro j hj
    have hjL : j + 1 ≤ L := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hc : ((j + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hjL
    rw [ite_eq_left (hc.trans_lt hs)]
  rw [Finset.sum_congr rfl h]
  simp

theorem integer_cuts {L : ℕ} {s : ℝ} (hs : 0 ≤ s) (hL : s ≤ L) :
    0 ≤ s - integerCutCount L s ∧
      s - integerCutCount L s ≤ if 0 < s then 1 else 0 := by
  induction L with
  | zero =>
      have hz : s = 0 := le_antisymm (by simpa using hL) hs
      simp [hz, integerCutCount]
  | succ L ih =>
      have hlast : ¬ ((L + 1 : ℕ) : ℝ) < s := not_lt.mpr hL
      rw [integerCutCount_succ, ite_eq_right hlast, add_zero]
      by_cases hsmall : s ≤ (L : ℝ)
      · exact ih hsmall
      · have hbig : (L : ℝ) < s := lt_of_not_ge hsmall
        rw [integerCutCount_above L hbig]
        have hpos : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg L) hbig
        rw [ite_eq_left hpos]
        push_cast at hL
        constructor <;> linarith

theorem rank_error_bounds {traceValue rankValue supportRank δ : ℝ}
    (herror : 0 ≤ traceValue - rankValue)
    (hbound : traceValue - rankValue ≤ supportRank)
    (hsmall : supportRank < δ) :
    traceValue - δ < rankValue ∧ rankValue ≤ traceValue := by
  constructor <;> linarith

end CuntzComparison

end OAI
