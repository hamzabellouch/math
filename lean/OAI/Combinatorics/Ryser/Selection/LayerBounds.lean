import OAI.Combinatorics.Ryser.Selection.SmallSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_powers_le_positive_index_bound (T : Finset ℕ) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hsize : ∀ m ∈ T, m ≤ N) :
    (∑ m ∈ T, B ^ m) ≤ (N : ℝ) * (max 1 B) ^ N := by
  have hsub : T ⊆ Finset.Icc 1 N := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hpositive m hm, hsize m hm⟩
  have hcard : T.card ≤ N := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hmax0 : (0 : ℝ) ≤ max 1 B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  calc
    (∑ m ∈ T, B ^ m) ≤ ∑ _m ∈ T, (max 1 B) ^ N := by
      apply Finset.sum_le_sum
      intro m hm
      exact (pow_le_pow_left₀ hB (le_max_right 1 B) m).trans
        (pow_le_pow_right₀ (le_max_left 1 B) (hsize m hm))
    _ = (T.card : ℝ) * (max 1 B) ^ N := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (max 1 B) ^ N :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (pow_nonneg hmax0 N)

theorem weighted_unused_error_eq_power (B δ : ℝ) (K m : ℕ) :
    B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))) =
      (B * Real.exp (2 - (K : ℝ) * δ)) ^ m := by
  have hexponent : -(((K : ℝ) * δ - 2) * (m : ℝ)) =
      (m : ℝ) * (2 - (K : ℝ) * δ) := by ring
  rw [hexponent, Real.exp_nat_mul, mul_pow]

theorem large_layer_sum_le (T : Finset ℕ) (D K q : ℕ) (B J c c1 δ : ℝ)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hc1 : 0 < c1)
    (hpositive : ∀ m ∈ T, 1 ≤ m)
    (hsize : ∀ m ∈ T, m ≤ D * q)
    (hlarge : ∀ m ∈ T, c1 * (q : ℝ) < (m : ℝ))
    (hratio : B * Real.exp (2 - (K : ℝ) * δ) ≤ 1 / 2) :
    (∑ m ∈ T, B ^ m *
      (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))))) ≤
      J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
        Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
          (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
  have hdensity :
      (∑ m ∈ T, B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)))) ≤
        J * ((D : ℝ) * (q : ℝ)) * (max 1 B) ^ (D * q) *
          Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) := by
    calc
      _ = (∑ m ∈ T, B ^ m) *
          (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) := by
        rw [Finset.sum_mul]
      _ ≤ ((D * q : ℕ) : ℝ) * (max 1 B) ^ (D * q) *
          (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (sum_powers_le_positive_index_bound T (D * q) B hB hpositive hsize)
          (mul_nonneg hJ (Real.exp_pos _).le)
      _ = _ := by
        rw [Nat.cast_mul]
        ring
  have hratio0 : 0 ≤ B * Real.exp (2 - (K : ℝ) * δ) :=
    mul_nonneg hB (Real.exp_pos _).le
  have hunused :
      (∑ m ∈ T, B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ)))) ≤
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
    calc
      _ = ∑ m ∈ T, (B * Real.exp (2 - (K : ℝ) * δ)) ^ m := by
        apply Finset.sum_congr rfl
        intro m _
        exact weighted_unused_error_eq_power B δ K m
      _ ≤ ∑ m ∈ T, (1 / 2 : ℝ) ^ m :=
        Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ hratio0 hratio m)
      _ ≤ (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)) := by
        apply sum_half_pow_le_cutoff
        intro m hm
        exact (Nat.floor_lt (mul_nonneg hc1.le (Nat.cast_nonneg q))).mpr (hlarge m hm)
  calc
    _ = (∑ m ∈ T, B ^ m * (J * Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)))) +
        ∑ m ∈ T, B ^ m * Real.exp (-(((K : ℝ) * δ - 2) * (m : ℝ))) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add hdensity hunused

end RyserCoveringCounterexample.Selection

end OAI
