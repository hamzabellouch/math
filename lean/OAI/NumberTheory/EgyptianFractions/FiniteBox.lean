import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Counting positive integer functions in a varying finite box. -/
theorem finite_ncard_le_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℕ)) (B : ι → ℕ)
    (hS : ∀ n ∈ S, ∀ i, 1 ≤ n i ∧ n i ≤ B i) :
    S.Finite ∧ S.ncard ≤ ∏ i, B i := by
  classical
  have hsub : S ⊆ Set.pi Set.univ (fun i => Set.Icc 1 (B i)) := by
    intro n hn i _
    exact hS n hn i
  have hcard : (Set.pi Set.univ (fun i => Set.Icc 1 (B i))).encard =
      (∏ i, B i : ℕ) := by
    rw [Set.encard_pi_eq_prod_encard, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [← (Set.finite_Icc 1 (B i)).cast_ncard_eq]
    simp
  apply Set.encard_le_coe_iff_finite_ncard_le.mp
  rw [← hcard]
  exact Set.encard_le_encard hsub

/-- Geometric exponent sum for the denominator box. -/
theorem sum_two_pow_fin (k : ℕ) :
    (∑ i : Fin k, 2 ^ i.val) = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    have hpos : 0 < 2 ^ k := pow_pos (by decide) _
    omega

/-- The denominator box appearing in the counting bound has the stated size. -/
theorem prod_egyptian_bounds (k : ℕ) :
    (∏ i : Fin k, k ^ (2 ^ i.val)) = k ^ (2 ^ k - 1) := by
  rw [Finset.prod_pow_eq_pow_sum, sum_two_pow_fin]

/-- Pointwise denominator bounds give finiteness and the sharp box-count estimate. -/
theorem finite_ncard_le_egyptian_box (k : ℕ) (S : Set (Fin k → ℕ))
    (hpos : ∀ n ∈ S, ∀ i, 1 ≤ n i)
    (hbound : ∀ n ∈ S, ∀ i, n i ≤ k ^ (2 ^ i.val)) :
    S.Finite ∧ S.ncard ≤ k ^ (2 ^ k - 1) := by
  simpa only [prod_egyptian_bounds] using
    finite_ncard_le_box S (fun i => k ^ (2 ^ i.val))
      (fun n hn i => ⟨hpos n hn i, hbound n hn i⟩)

end Problem337

end

end OAI
