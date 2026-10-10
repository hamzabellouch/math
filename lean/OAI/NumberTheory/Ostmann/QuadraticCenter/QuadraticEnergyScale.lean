import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem harmonic_le_nat_real (q : ℕ) : (harmonic q : ℝ) ≤ q := by
  calc
    _ = ∑ i ∈ Finset.range q, (((i + 1 : ℕ) : ℝ))⁻¹ := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ ∑ _i ∈ Finset.range q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos i)
    _ = _ := by simp

theorem divisor_lcm_harmonic_le {L d e S : ℕ} (hL : 0 < L)
    (hd : d ∣ L) (he : e ∣ L) (hS : L ^ 2 ≤ S) :
    (Nat.lcm d e : ℝ) * (harmonic (Nat.lcm d e) : ℝ) ≤ S := by
  have hq : Nat.lcm d e ≤ L := Nat.le_of_dvd hL (Nat.lcm_dvd hd he)
  have hq' : (Nat.lcm d e : ℝ) ≤ L := by exact_mod_cast hq
  have hS' : (L : ℝ) ^ 2 ≤ S := by exact_mod_cast hS
  calc
    _ ≤ (Nat.lcm d e : ℝ) * (Nat.lcm d e : ℝ) :=
      mul_le_mul_of_nonneg_left (harmonic_le_nat_real _) (Nat.cast_nonneg _)
    _ ≤ (L : ℝ) * L := mul_self_le_mul_self (Nat.cast_nonneg _) hq'
    _ ≤ _ := by simpa only [pow_two] using hS'

theorem divisor_lcm_harmonic_le_of_fourth_power {L d e S : ℕ} (hL : 0 < L)
    (hd : d ∣ L) (he : e ∣ L) (hS : L ^ 4 ≤ S) :
    (Nat.lcm d e : ℝ) * (harmonic (Nat.lcm d e) : ℝ) ≤ S := by
  apply divisor_lcm_harmonic_le hL hd he
  have hL1 : 1 ≤ L := hL
  have hh : L ^ 2 ≤ L ^ 4 := by nlinarith [sq_nonneg ((L : ℤ) - 1)]
  exact hh.trans hS

end Ostmann.QuadraticCenter

end OAI
