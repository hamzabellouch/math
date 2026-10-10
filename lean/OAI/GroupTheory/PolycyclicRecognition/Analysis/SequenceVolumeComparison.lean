import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePackingAsymptotics

namespace OAI

/-! # Exponential volume comparison along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

theorem subexponential_upper_polynomial {D : ℝ} (hD : 0 < D) (k : ℕ) :
    HasSubexponentialUpperBound (fun r => D * (1 + r) ^ k) := by
  intro ε hε
  filter_upwards [eventually_logarithmic_error_le (k : ℝ) (Real.log D) hε,
    eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h1 : 0 < 1 + r := by positivity
  apply (Real.log_le_iff_le_exp (mul_pos hD (pow_pos h1 k))).mp
  rw [Real.log_mul hD.ne' (pow_ne_zero _ h1.ne'), Real.log_pow]
  have hlog : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log h1 (by linarith)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlog hk]

theorem exponent_le_of_sequence_polynomial_bound
    {scale f : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q D : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hD : 0 < D) (k : ℕ)
    (hbound : ∀ᶠ n in atTop,
      f n * Real.exp (scale n * p) ≤ D * (1 + scale n) ^ k * Real.exp (scale n * q)) :
    p ≤ q :=
  exponent_le_of_sequence_subexponential_bounds hs hf
    ((subexponential_upper_polynomial hD k).along_sequence hs) hbound

theorem exponent_le_of_sequence_separated_counts
    {scale f : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q D : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hD : 0 < D)
    {Q : ℝ≥0∞} (hQ : Q < ⊤) (k : ℕ)
    (hcount : ∀ᶠ n in atTop, ∃ N : ℕ,
      ENNReal.ofReal (f n) * ENNReal.ofReal (Real.exp (scale n * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + scale n) ^ k * Real.exp (scale n * q)) : p ≤ q := by
  apply exponent_le_of_sequence_polynomial_bound hs hf
    (show 0 < D * Q.toReal + 1 by positivity) k
  filter_upwards [hcount, hf.eventually_pos, hs.eventually (eventually_ge_atTop (0 : ℝ))]
    with n hn hfpos hrpos
  obtain ⟨N, hlow, hupp⟩ := hn
  have hfinite : (N : ℝ≥0∞) * Q ≠ ⊤ := ENNReal.mul_ne_top (by simp) hQ.ne
  have hl := ENNReal.toReal_mono hfinite hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfpos.le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_natCast] at hl
  calc
    f n * Real.exp (scale n * p) ≤ (N : ℝ) * Q.toReal := hl
    _ ≤ (D * (1 + scale n) ^ k * Real.exp (scale n * q)) * Q.toReal :=
      mul_le_mul_of_nonneg_right hupp ENNReal.toReal_nonneg
    _ = (D * Q.toReal) * (1 + scale n) ^ k * Real.exp (scale n * q) := by ring
    _ ≤ _ := by gcongr; linarith

end PolycyclicRecognition

end OAI
