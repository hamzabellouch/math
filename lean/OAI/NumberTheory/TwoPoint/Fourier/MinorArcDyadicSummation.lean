import OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameters
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Log

namespace OAI

/-! Summing the reciprocal logarithmic saving over dyadic prime blocks. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_dyadic_prime_bounds {p j : ℕ} (hp : 0 < p) (hj : Nat.log 2 p = j) :
    2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j := by
  have hl := Nat.pow_log_le_self 2 hp.ne'
  have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [hj] at hl hu
  rw [pow_succ] at hu
  exact ⟨hl, by omega⟩

lemma minor_arc_dyadic_index_pos {p : ℕ} (hp : 2 ≤ p) : 1 ≤ Nat.log 2 p := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  simpa using hp

lemma minor_arc_dyadic_log_sum (J : Finset ℕ) (N : ℕ)
    (hJ : J ⊆ Icc 1 N) :
    (∑ j ∈ J, 1 / Real.log ((2 : ℝ) ^ j)) ≤
      (1 + Real.log (N : ℝ)) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfull : (∑ j ∈ Icc 1 N, 1 / Real.log ((2 : ℝ) ^ j)) =
      (harmonic N : ℝ) / Real.log 2 := by
    simp only [Real.log_pow]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, sum_div]
    apply sum_congr rfl
    intro j _
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  calc
    _ ≤ ∑ j ∈ Icc 1 N, 1 / Real.log ((2 : ℝ) ^ j) := by
      apply sum_le_sum_of_subset_of_nonneg hJ
      intro j hj _
      rw [Real.log_pow]
      positivity
    _ = (harmonic N : ℝ) / Real.log 2 := hfull
    _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log N) hlog2.le

lemma minor_arc_weighted_dyadic_log_sum (J : Finset ℕ) (N : ℕ)
    (hJ : J ⊆ Icc 1 N) (K : ℝ) (hK : 0 ≤ K) (S : ℕ → ℝ)
    (hS : ∀ j ∈ J, S j ≤ K / Real.log ((2 : ℝ) ^ j)) :
    (∑ j ∈ J, S j) ≤ K * (1 + Real.log (N : ℝ)) / Real.log 2 := by
  calc
    _ ≤ ∑ j ∈ J, K / Real.log ((2 : ℝ) ^ j) := sum_le_sum hS
    _ = K * ∑ j ∈ J, 1 / Real.log ((2 : ℝ) ^ j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ K * ((1 + Real.log (N : ℝ)) / Real.log 2) :=
      mul_le_mul_of_nonneg_left (minor_arc_dyadic_log_sum J N hJ) hK
    _ = _ := by ring

end TwoPointCorrelations

end OAI
