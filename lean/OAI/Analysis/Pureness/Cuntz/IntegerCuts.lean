import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI
namespace CuntzPureness

noncomputable def integerCutCount (l : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range l, if (j : ℝ) + 1 < t then 1 else 0

theorem integerCutCount_bounds (l : ℕ) (t : ℝ) (ht : 0 ≤ t) (hl : t ≤ l) :
    0 ≤ t - integerCutCount l t ∧
      t - integerCutCount l t ≤ if 0 < t then 1 else 0 := by
  induction l with
  | zero =>
    have h : t = 0 := le_antisymm (by simpa using hl) ht
    subst t
    simp [integerCutCount]
  | succ l ih =>
    by_cases htl : t ≤ (l : ℝ)
    · have hlast : ¬ (l : ℝ) + 1 < t := by linarith
      simpa [integerCutCount, Finset.sum_range_succ, hlast] using ih htl
    · have hlt : (l : ℝ) < t := lt_of_not_ge htl
      have hpos : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg l) hlt
      have hlast : ¬ (l : ℝ) + 1 < t := by exact not_lt_of_ge (by simpa using hl)
      have hcount : integerCutCount l t = l := by
        unfold integerCutCount
        have hone : ∀ j ∈ Finset.range l, (if (j : ℝ) + 1 < t then (1 : ℝ) else 0) = 1 := by
          intro j hj
          have hjl : j + 1 ≤ l := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
          have hjlr : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
          simp [lt_of_le_of_lt hjlr hlt]
        rw [Finset.sum_congr rfl hone]
        simp
      have hnext : integerCutCount (l + 1) t = l := by
        simpa [integerCutCount, Finset.sum_range_succ, hlast] using hcount
      rw [hnext, ite_eq_left hpos]
      constructor <;> push_cast at hl <;> linarith

theorem integerCutCount_zero (l : ℕ) : integerCutCount l 0 = 0 := by
  unfold integerCutCount
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  simp [show ¬ (j : ℝ) + 1 < 0 by linarith]

theorem integerCutCount_at_positive_integer (l k : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) :
    (k : ℝ) - integerCutCount l k = 1 := by
  have hset : integerCutCount l k = ∑ j ∈ Finset.range l, if j < k - 1 then (1 : ℝ) else 0 := by
    unfold integerCutCount
    apply Finset.sum_congr rfl
    intro j hj
    have heq : (j : ℝ) + 1 < k ↔ j < k - 1 := by
      constructor
      · intro h
        have : j + 1 < k := by exact_mod_cast h
        omega
      · intro h
        have : j + 1 < k := by omega
        exact_mod_cast this
    simp only [heq]
  rw [hset]
  have hs : (∑ j ∈ Finset.range l, if j < k - 1 then (1 : ℝ) else 0) = k - 1 := by
    rw [← Finset.sum_filter]
    have hf : (Finset.range l).filter (fun j => j < k - 1) = Finset.range (k - 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf]
    simp [Nat.cast_sub hk]
  rw [hs]
  linarith
end CuntzPureness

end OAI
