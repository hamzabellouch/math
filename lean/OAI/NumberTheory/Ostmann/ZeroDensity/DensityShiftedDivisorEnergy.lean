import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierMean

namespace OAI

/-! # Divisor energies for the short head and the far coefficient blocks -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityVerticalCoeff_square (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a σ n‖ ^ 2 = ‖a n‖ ^ 2 / (n : ℝ) ^ (2 * σ) := by
  rw [densityVerticalCoeff_norm a σ n hn, div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  norm_num
  ring

 theorem density_divisor_shifted_head (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c) n‖ ^ 2) ≤
        (1 + Real.log N) ^ 4 := by
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans (density_divisor_square_harmonic N)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [densityVerticalCoeff_square _ _ n (Finset.mem_Icc.mp hn).1]
  simp only [Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  calc
    (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (n : ℝ) ^ (2 * (1 / 2 + c)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)

 theorem density_divisor_shifted_tail (S : Finset ℕ) (M N : ℕ) (hM : 1 ≤ M)
    (hS : S ⊆ Finset.Icc M N) :
    (∑ n ∈ S,
      ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + (1 : ℝ)) n‖ ^ 2) ≤
        (N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ 3 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 / (M : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      have hMn := (Finset.mem_Icc.mp (hS hn)).1
      have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < M) hMn
      rw [densityVerticalCoeff_square _ _ n hnpos]
      norm_num only [Complex.norm_natCast, show (2 : ℝ) * (1 / 2 + 1) = 3 by norm_num,
        Real.rpow_natCast]
      have hp : (M : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
        pow_le_pow_left₀ hMp.le (by exact_mod_cast hMn) 3
      convert div_le_div_of_nonneg_left (sq_nonneg (n.divisors.card : ℝ)) (pow_pos hMp 3) hp using 1
      simp only [Real.rpow_ofNat]
    _ = (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ 3 := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hMp.le 3)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1,
          (Finset.mem_Icc.mp (hS hn)).2⟩
      · intro n _ _
        positivity
    _ ≤ _ := div_le_div_of_nonneg_right (density_divisor_square_sum N) (pow_nonneg hMp.le 3)

end Ostmann

end OAI
