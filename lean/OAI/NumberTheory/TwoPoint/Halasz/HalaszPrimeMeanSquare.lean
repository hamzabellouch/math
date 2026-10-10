import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeWindows

namespace OAI

/-! A prime-supported mean-value theorem with one von Mangoldt weight,
proved from the Brun--Titchmarsh theorem and the exact Fourier
kernel. This is the sparse mean-square input to Halasz's argument. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators

/-- Arbitrary complex prime coefficients are permitted. The constant is
independent of the upper end of the finite prime set. -/
theorem halasz_prime_mean_square : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T : ℝ) (P : Finset ℕ), B ≤ T →
      (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) → ∀ a : ℕ → ℂ,
      (∫ t in -T..T,
        ‖mrtExponentialPolynomial P
          (fun p => a p * ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t‖ ^ 2) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / (p : ℝ)) := by
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_windows_above_square
  refine ⟨Real.exp 1 * (16 * C), B, by positivity, hB, ?_⟩
  intro T P hBT hP a
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (hB.trans hBT)
  have hw : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le))
      (Nat.cast_nonneg _)
  have hrow : ∀ p ∈ P,
      (∑ q ∈ P, (Real.log (q : ℝ) / (q : ℝ)) *
        (2 * T / (1 + T ^ 2 * (-Real.log (p : ℝ) - -Real.log (q : ℝ)) ^ 2))) ≤
          16 * C := by
    intro p hp
    have hh := halasz_frequency_row_of_windows P (fun q => Real.log (q : ℝ))
      (fun q => Real.log (q : ℝ) / (q : ℝ)) (Real.log (p : ℝ)) hT hC.le hw
      (hwindow T P hBT hP)
    convert hh using 1
    apply sum_congr rfl
    intro q _
    rw [show (-Real.log (p : ℝ) - -Real.log (q : ℝ)) ^ 2 =
      (Real.log (q : ℝ) - Real.log (p : ℝ)) ^ 2 by ring]
  exact halasz_mean_square_of_weighted_rows P a
    (fun p => Real.log (p : ℝ) / (p : ℝ)) (fun p => -Real.log (p : ℝ)) hT hw hrow

end TwoPointCorrelations

end OAI
