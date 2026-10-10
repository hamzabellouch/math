import OAI.NumberTheory.Ostmann.Arithmetic.LcmFrequencySum
import OAI.NumberTheory.Ostmann.Supply.MultiplierWeightedBudget

namespace OAI

/-! # The elementary second moment of divisor coefficients

Pairs of divisors are counted by their least common multiple. The
harmonic-cube estimate gives the logarithmic third power without a
pointwise divisor bound.
-/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_divisor_count_as_sum (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (n.divisors.card : ℝ) = ∑ d ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0 := by
  have he : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, by have hpos := (Finset.mem_Icc.mp hn).1; omega⟩
    · intro h
      have hpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hdpos := Nat.pos_of_dvd_of_pos h.1 hpos
      exact ⟨⟨hdpos, (Nat.le_of_dvd hpos h.1).trans (Finset.mem_Icc.mp hn).2⟩, h.1⟩
  rw [← Finset.sum_filter, he]
  simp

 theorem density_divisor_square_as_sum (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (n.divisors.card : ℝ) ^ 2 = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      if d.lcm e ∣ n then (1 : ℝ) else 0 := by
  rw [density_divisor_count_as_sum N n hn, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [Nat.lcm_dvd_iff, hd, he]

 theorem density_divisor_square_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((N / d.lcm e : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun n hn => density_divisor_square_as_sum N n hn)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast positiveMultipliers_dvd_card N (d.lcm e)
    _ ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro e _
      simpa only [div_eq_mul_inv] using
        (Nat.cast_div_le (m := N) (n := d.lcm e) (α := ℝ))
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_lcm_sum_le_log_cube N) (Nat.cast_nonneg _)

end Ostmann

end OAI
