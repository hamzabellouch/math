import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeSumInputs
import OAI.NumberTheory.Ostmann.Supply.SquarefreeEulerBound

namespace OAI

/-! # An elementary logarithmic bound for the reciprocal-prime sum -/

namespace Ostmann

open scoped BigOperators

private theorem prime_dyadic_reciprocal_bound (S : Finset ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hS : ∀ p ∈ S, p.Prime ∧ 2 ^ j ≤ p ∧ p ≤ 2 ^ (j + 1)) :
    (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 4 / (j : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hd : 0 < (2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) := by positivity
  have hlogsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log 4 * (2 ^ (j + 1) : ℕ) := by
    apply le_trans _ (prime_log_weight_le (2 ^ (j + 1)))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨(hS p hp).2.2, (hS p hp).1⟩
    · intro p hp hn
      exact Real.log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hS p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlow : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hlo
      have hlog : (j : ℝ) * Real.log 2 ≤ Real.log p := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hlow
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hp0 hd).mpr
      simp only [one_mul]
      calc
        _ ≤ (p : ℝ) * Real.log p := mul_le_mul hlow hlog (by positivity) hp0.le
        _ = _ := mul_comm _ _
    _ = (∑ p ∈ S, Real.log (p : ℝ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (Real.log 4 * (2 ^ (j + 1) : ℕ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      div_le_div_of_nonneg_right hlogsum hd.le
    _ = 4 / (j : ℝ) := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      ring

theorem prime_reciprocal_sum_le_harmonic (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (harmonic (Nat.log 2 N) : ℝ) := by
  classical
  let P := Nat.primesLE N
  let K := Nat.log 2 N
  have hmaps (p : ℕ) (hp : p ∈ P) : Nat.log 2 p ∈ Finset.Icc 1 K := by
    have hprime := Nat.prime_of_mem_primesLE hp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.log_pos (by decide) hprime.two_le
    · exact Nat.log_mono_right (Nat.le_of_mem_primesLE hp)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 K, 4 / (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply prime_dyadic_reciprocal_bound _ j (Finset.mem_Icc.mp hj).1
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      refine ⟨Nat.prime_of_mem_primesLE hp, ?_, ?_⟩
      · rw [← he]
        exact Nat.pow_log_le_self 2 (Nat.prime_of_mem_primesLE hp).ne_zero
      · rw [← he]
        exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le
    _ = 4 * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, Finset.mul_sum]

theorem prime_reciprocal_sum_le_log (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (1 + Real.log (Nat.log 2 N)) := by
  exact (prime_reciprocal_sum_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by norm_num))

end Ostmann

end OAI
