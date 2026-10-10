import OAI.NumberTheory.TwoPointCorrelations.HalaszDoubleConvolution
import OAI.NumberTheory.TwoPointCorrelations.HalaszDenominatorMass

namespace OAI

/-! The ordinary mean reduces to the adaptive double prime convolution,
with an explicit N log log N error. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszDenominatorConstant : ℝ :=
  -Real.log (Real.log 2) + 2 * halaszMertensConstant / Real.log 2

theorem halasz_double_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N L‖ + (N : ℝ) *
        (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1 + halaszInnerErrorConstant *
            (Real.log (Real.log N) + halaszDenominatorConstant)) := by
  have hmass := halasz_denominator_prime_mass hL hLN
  have hm := halasz_double_convolution_error f hf hmul N hL
  have hC : 0 ≤ halaszInnerErrorConstant * (N : ℝ) :=
    mul_nonneg halaszInnerErrorConstant_nonneg (Nat.cast_nonneg _)
  have herr : ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
      halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        (Real.log (Real.log N) + halaszDenominatorConstant) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [halaszDenominatorConstant, sub_eq_add_neg, add_assoc] using hmass
  have hn := norm_add_le (halaszDoubleConvolution f N L)
    (halaszPrimeBandConvolution f N L ((N : ℝ) / 2) - halaszDoubleConvolution f N L)
  rw [add_sub_cancel] at hn
  have ht := halasz_truncated_convolution_mean_bound f hf hmul N hL hLN
  nlinarith

noncomputable def halaszDoubleErrorConstant : ℝ :=
  4 + (Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1) +
    halaszInnerErrorConstant * (1 + |halaszDenominatorConstant|)

lemma halaszDoubleErrorConstant_nonneg : 0 ≤ halaszDoubleErrorConstant := by
  have hm := halaszMertensConstant_nonneg
  have hp := halaszPrimePowerConstant_nonneg
  have hi := halaszInnerErrorConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold halaszDoubleErrorConstant
  positivity

/-- The logarithmic-fourth-power prime cutoff used in the mean-value proof. -/
theorem halasz_double_mean_log_fourth (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hlog : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hL : 1 ≤ Real.log (N : ℝ) ^ 4)
    (hLN : Real.log (N : ℝ) ^ 4 ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N (Real.log (N : ℝ) ^ 4)‖ +
        halaszDoubleErrorConstant * (N : ℝ) * Real.log (Real.log N) := by
  have hb := halasz_double_mean_bound f hf hmul N hL hLN
  have hpow : Real.log (Real.log (N : ℝ) ^ 4) = 4 * Real.log (Real.log (N : ℝ)) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hb
  have hA : 0 ≤ Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1 := by
    have hm := halaszMertensConstant_nonneg
    have hp := halaszPrimePowerConstant_nonneg
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hi := halaszInnerErrorConstant_nonneg
  have hsmall := mul_le_mul_of_nonneg_left hlog hA
  have hD : halaszDenominatorConstant ≤ |halaszDenominatorConstant| *
      Real.log (Real.log (N : ℝ)) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have hprod := mul_le_mul_of_nonneg_left hD hi
  have hscalar : 4 * Real.log (Real.log (N : ℝ)) + Real.log 2 +
      3 * halaszMertensConstant + halaszPrimePowerConstant + 1 +
      halaszInnerErrorConstant * (Real.log (Real.log N) + halaszDenominatorConstant) ≤
      halaszDoubleErrorConstant * Real.log (Real.log N) := by
    unfold halaszDoubleErrorConstant
    nlinarith
  have hmulN := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

/-- The larger fixed logarithmic cutoff needed by the narrow-window
truncation. The deletion error still has order N log log N. -/
theorem halasz_double_mean_log_sixteenth (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hlog : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hL : 1 ≤ Real.log (N : ℝ) ^ 16)
    (hLN : Real.log (N : ℝ) ^ 16 ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N (Real.log (N : ℝ) ^ 16)‖ +
        (halaszDoubleErrorConstant + 12) * (N : ℝ) * Real.log (Real.log N) := by
  have hb := halasz_double_mean_bound f hf hmul N hL hLN
  have hpow : Real.log (Real.log (N : ℝ) ^ 16) = 16 * Real.log (Real.log (N : ℝ)) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hb
  have hA : 0 ≤ Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1 := by
    have hm := halaszMertensConstant_nonneg
    have hp := halaszPrimePowerConstant_nonneg
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hi := halaszInnerErrorConstant_nonneg
  have hsmall := mul_le_mul_of_nonneg_left hlog hA
  have hD : halaszDenominatorConstant ≤ |halaszDenominatorConstant| *
      Real.log (Real.log (N : ℝ)) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have hprod := mul_le_mul_of_nonneg_left hD hi
  have hscalar : 16 * Real.log (Real.log (N : ℝ)) + Real.log 2 +
      3 * halaszMertensConstant + halaszPrimePowerConstant + 1 +
      halaszInnerErrorConstant * (Real.log (Real.log N) + halaszDenominatorConstant) ≤
      (halaszDoubleErrorConstant + 12) * Real.log (Real.log N) := by
    unfold halaszDoubleErrorConstant
    nlinarith
  have hmulN := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end TwoPointCorrelations

end OAI
