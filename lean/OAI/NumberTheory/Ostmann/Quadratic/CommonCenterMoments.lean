import Mathlib.Data.Nat.Factorial.Basic
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenter

namespace OAI

/-! # The falling-factorial moment step in common-center extraction -/

namespace Ostmann

open scoped BigOperators

theorem descFactorial_gap_le (r k d : ℕ) (hd : d ≤ k) :
    r.descFactorial k ≤ r ^ d * r.descFactorial (k - d) := by
  rw [← Nat.descFactorial_mul_descFactorial (Nat.sub_le k d), Nat.sub_sub_self hd]
  apply Nat.mul_le_mul_right
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le r _) d)

/-- Small matching sets contribute only a power of the threshold times a lower moment. -/
theorem smallCenter_factorial_moment_le {I : Type*} [Fintype I]
    (r : I → ℕ) (k d : ℕ) (hd : d ≤ k) (A : ℝ) (hA : 0 ≤ A) :
    (∑ i : I, if (r i : ℝ) < A then ((r i).descFactorial k : ℝ) else 0) ≤
      A ^ d * ∑ i : I, ((r i).descFactorial (k - d) : ℝ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have h : ((r i).descFactorial k : ℝ) ≤
        (r i : ℝ) ^ d * ((r i).descFactorial (k - d) : ℝ) := by
      exact_mod_cast descFactorial_gap_le (r i) k d hd
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hi.le d) (Nat.cast_nonneg _))
  · exact mul_nonneg (pow_nonneg hA _) (Nat.cast_nonneg _)

/-- The mass surviving the small-set removal is a moment of high matching sets. -/
theorem highCenter_factorial_moment_ge {I : Type*} [Fintype I]
    (r : I → ℕ) (k d : ℕ) (hd : d ≤ k) (A B L : ℝ) (hA : 0 ≤ A)
    (hlo : (∑ i : I, ((r i).descFactorial (k - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ i : I, ((r i).descFactorial k : ℝ)) :
    L - A ^ d * B ≤
      ∑ i : I, if A ≤ (r i : ℝ) then ((r i).descFactorial k : ℝ) else 0 := by
  classical
  have hsmall := (smallCenter_factorial_moment_le r k d hd A hA).trans
    (mul_le_mul_of_nonneg_left hlo (pow_nonneg hA _))
  have hsplit :
      (∑ i : I, ((r i).descFactorial k : ℝ)) =
      (∑ i : I, if (r i : ℝ) < A then ((r i).descFactorial k : ℝ) else 0) +
      (∑ i : I, if A ≤ (r i : ℝ) then ((r i).descFactorial k : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (r i : ℝ) < A
    · simp only [hi, not_le.mpr hi, ite_true, ite_false, add_zero]
    · simp only [hi, le_of_not_gt hi, ite_true, ite_false, zero_add]
  linarith

/-- The two factorial moment estimates in `quad-lift-factorials` produce a common center. -/
theorem exists_commonCenter_from_factorial_moments {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) (k d : ℕ) (hd : d ≤ k + 1) (A K B L : ℝ)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2)
    (hlo : (∑ i : I, ((S i).card.descFactorial (k + 1 - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ i : I, ((S i).card.descFactorial (k + 1) : ℝ))
    (hpositive : 0 < L - A ^ d * B) :
    ∃ i : I, A ≤ ((S i).card : ℝ) ∧
      L - A ^ d * B ≤ 2 * (Fintype.card P : ℝ) * ((S i).card : ℝ) ^ k := by
  classical
  let H := {i : I // A ≤ ((S i).card : ℝ)}
  have hsum : (∑ i : H, ((S i.1).card.descFactorial (k + 1) : ℝ)) =
      ∑ i : I, if A ≤ ((S i).card : ℝ) then ((S i).card.descFactorial (k + 1) : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun i : I => A ≤ ((S i).card : ℝ))
      (Finset.univ.filter fun i : I => A ≤ ((S i).card : ℝ))
      (by intro i; simp) (fun i => ((S i).card.descFactorial (k + 1) : ℝ))).symm
  have hh : L - A ^ d * B ≤ ∑ i : H, ((S i.1).card.descFactorial (k + 1) : ℝ) := by
    rw [hsum]
    exact highCenter_factorial_moment_ge (fun i => (S i).card) (k + 1) d hd A B L hA.le hlo hhi
  have hH : Nonempty H := by
    by_contra h
    have : IsEmpty H := ⟨fun i => h ⟨i⟩⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hh
    linarith
  let : Nonempty H := hH
  have hpows : L - A ^ d * B ≤ ∑ i : H, ((S i.1).card : ℝ) ^ (k + 1) := by
    apply hh.trans
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Nat.descFactorial_le_pow (S i.1).card (k + 1)
  obtain ⟨i, hi⟩ := exists_commonCenter_of_moment (fun i : H => S i.1) A K
    (L - A ^ d * B) k hA hK (fun i => i.2)
    (fun i j hij => hinter i.1 j.1 (fun h => hij (Subtype.ext h))) hsmall hpows
  exact ⟨i.1, i.2, hi⟩

end Ostmann

end OAI
