import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Construction.TransferArithmetic

namespace OAI

/-! # The actual finite range of a transferred frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A fixed covering range for the signed output frequency. Zero is excluded
in the summand, so the same interval also works when the range is empty. -/
def transferFrequencyRange (V : ℕ) : Finset ℤ := Finset.Icc (-(V : ℤ)) V

theorem mem_transferFrequencyRange (V : ℕ) (s : ℤ) :
    s ∈ transferFrequencyRange V ↔ s.natAbs ≤ V := by
  simp only [transferFrequencyRange, Finset.mem_Icc]
  rw [← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast (Iff.rfl : s.natAbs ≤ V ↔ s.natAbs ≤ V)

/-- The product ranges supply the frequency cutoff without rounding a
quotient or introducing an independent frequency assumption. -/
theorem transferred_frequency_bound (M L R B H V : ℕ) (s v w : ℤ)
    (hM : 0 < M) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H)
    (hscale : 2 * B * H ≤ V * M)
    (hrel : v * R - w * L = s * M) : s.natAbs ≤ V := by
  have he : s.natAbs * M = (v * R - w * L).natAbs := by
    rw [hrel, Int.natAbs_mul, Int.natAbs_natCast]
  have hnum : (v * R - w * L).natAbs ≤ 2 * B * H := by
    calc
      _ ≤ (v * R).natAbs + (w * L).natAbs := Int.natAbs_sub_le _ _
      _ = v.natAbs * R + w.natAbs * L := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ B * H + B * H := Nat.add_le_add (Nat.mul_le_mul hv hR) (Nat.mul_le_mul hw hL)
      _ = 2 * B * H := by ring
  exact Nat.le_of_mul_le_mul_right ((he.trans_le hnum).trans hscale) hM

/-- One integer quotient contributes once, including its sign. -/
theorem transferred_frequency_sum (M : ℕ) (hM : 0 < M) (N : ℤ)
    (S : Finset ℤ) (hS : ∀ s : ℤ, s ≠ 0 → N = s * M → s ∈ S) (z : ℂ) :
    (if N ≠ 0 ∧ (M : ℤ) ∣ N then z else 0) =
      ∑ s ∈ S, if s ≠ 0 ∧ N = s * M then z else 0 := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  by_cases h : N ≠ 0 ∧ (M : ℤ) ∣ N
  · obtain ⟨s, hs, huniq⟩ := unique_transferred_frequency N M h.1 hM0 h.2
    rw [ite_eq_left h, Finset.sum_eq_single s]
    · rw [ite_eq_left hs]
    · intro t _ hts
      rw [ite_eq_right]
      intro ht
      exact hts (huniq t ht)
    · exact fun hnot => (hnot (hS s hs.1 hs.2)).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    apply h
    refine ⟨?_, ?_⟩
    · rw [he]
      exact mul_ne_zero hs hM0
    · rw [he]
      exact dvd_mul_left (M : ℤ) s

/-- A prime-product range is enough to cover every off-diagonal term by
its actual new root frequency. -/
theorem transferred_frequency_sum_bounded (M L R B H V : ℕ)
    (hM : 0 < M) (v w : ℤ) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H) (hscale : 2 * B * H ≤ V * M) (z : ℂ) :
    (if v * R - w * L ≠ 0 ∧ (M : ℤ) ∣ v * R - w * L then z else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v * R - w * L = s * M then z else 0 := by
  apply transferred_frequency_sum M hM
  intro s _ hs
  exact (mem_transferFrequencyRange V s).mpr
    (transferred_frequency_bound M L R B H V s v w hM hv hw hL hR hscale hs)

end Ostmann

end OAI
