import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDivisorMoment

namespace OAI

/-! # The harmonic second moment of the divisor function -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_harmonic_multiples (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (N / d), (k : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun k _ => d * k)
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hu := (Nat.le_div_iff_mul_le hd).mp hkN
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd hk1, by simpa only [mul_comm] using hu⟩, dvd_mul_right d k⟩
  · intro k _ l _ hkl
    exact Nat.eq_of_mul_eq_mul_left hd hkl
  · intro n hn
    obtain ⟨hnN, hdn⟩ := Finset.mem_filter.mp hn
    have hn1 := (Finset.mem_Icc.mp hnN).1
    have hdle : d ≤ n := Nat.le_of_dvd hn1 hdn
    refine ⟨n / d, Finset.mem_Icc.mpr ⟨Nat.div_pos hdle hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hnN).2⟩, ?_⟩
    exact Nat.mul_div_cancel' hdn
  · intro k _
    rw [Nat.cast_mul, mul_inv_rev, mul_comm]

 theorem density_harmonic_multiples_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (n : ℝ)⁻¹) ≤
      (d : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
  rw [density_harmonic_multiples N d hd]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.div_le_self N d)) (fun _ _ _ => by positivity)

 theorem density_divisor_square_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 / n) ≤
      (1 + Real.log N) ^ 4 := by
  let H : ℝ := ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  have hHlog : H ≤ 1 + Real.log N := by
    simpa only [H, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log N
  have hexp (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (n.divisors.card : ℝ) ^ 2 / n =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        if d.lcm e ∣ n then (n : ℝ)⁻¹ else 0 := by
    rw [density_divisor_square_as_sum N n hn, div_eq_mul_inv]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d.lcm e ∣ n), (n : ℝ)⁻¹ := by
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹ * H := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      apply density_harmonic_multiples_le
      exact Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹) * H := by simp only [Finset.sum_mul]
    _ ≤ (1 + Real.log N) ^ 3 * H :=
      mul_le_mul_of_nonneg_right (reciprocal_lcm_sum_le_log_cube N) hH
    _ ≤ (1 + Real.log N) ^ 3 * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left hHlog (pow_nonneg (hH.trans hHlog) 3)
    _ = _ := by ring

end Ostmann

end OAI
