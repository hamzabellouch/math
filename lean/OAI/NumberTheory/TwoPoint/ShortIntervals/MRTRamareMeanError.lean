import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSquareMean

namespace OAI

/-! The actual coefficient error made by replacing the corrected Ramaré
denominator with `ω_P(m)+1`.  The pointwise error is supported on prime
squares, so the preceding second-moment count applies directly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtRamareCorrection (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if finitePrimeDivisorCount P n = 0 then 0 else F n) -
    ∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0

theorem mrt_ramare_correction_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    ‖mrtRamareCorrection P F n‖ ≤ ‖F n‖ * mrtPrimeSquareCount P n := by
  unfold mrtRamareCorrection
  rw [mrt_ramare_identity P hP F n, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then ‖F n‖ else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hpn : p ∣ n
      · simp only [hpn, ite_true, Nat.mul_div_cancel' hpn]
        have he : p ∣ n / p ↔ p ^ 2 ∣ n := by
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn : p ∣ n / p ↔ p * p ∣ n)
        simpa only [he] using mrt_ramare_denominator_error P hp (F n) (m := n / p)
      · have hs : ¬p ^ 2 ∣ n := by
          intro hn
          apply hpn
          exact dvd_trans (by simpa only [pow_two] using (dvd_mul_right p p)) hn
        simp only [hpn, hs, ite_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp

theorem mrt_ramare_correction_oneBounded (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtRamareCorrection P F n‖ ≤ mrtPrimeSquareCount P n := by
  apply (mrt_ramare_correction_bound P hP F n).trans
  exact (mul_le_mul_of_nonneg_right (hF n hn) (mrtPrimeSquareCount_nonneg P n)).trans_eq
    (one_mul _)

/-- The literal denominator correction costs only the reciprocal square
mass in the normalized dyadic mean square.  Multiplicativity is not
needed for this error estimate. -/
theorem mrt_ramare_correction_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtRamareCorrection P F) N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  apply mrt_prime_square_dyadic_mean P hP _ hN _ hT
  intro n hn
  exact mrt_ramare_correction_oneBounded P hP F hF (hN.trans (mem_Ioc.mp hn).1)

end TwoPointCorrelations

end OAI
