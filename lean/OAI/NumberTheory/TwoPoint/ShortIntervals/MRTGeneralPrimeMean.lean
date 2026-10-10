import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralPrimeError

namespace OAI

/-! Mean-square control of the general multiplicative prime-extraction
error. The broad coarse window is handled before any sum over bins. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_prime_square_broad_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (4 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (16 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (4 * N), ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mul_nonneg (by norm_num) (mrtPrimeSquareCount_nonneg P n))
        (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Ioc N (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      have he (n : ℕ) : ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 =
          (4 * (N : ℝ)⁻¹ ^ 2) * (mrtPrimeSquareCount P n) ^ 2 := by ring
      simp_rw [he]
      rw [← mul_sum]
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Icc 1 (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ((4 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (4 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

/-- A prime-extraction error of size twice the square-divisor count has
an absolute mean-square cost on the complete coarse window. -/
theorem mrt_prime_square_broad_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc N (4 * N))
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (4 * N)) (N := 4 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * ((16 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_broad_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 128 * Real.exp 1 * (T / (N : ℝ) + 4) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI
