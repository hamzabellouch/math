import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! The bounded short-length cases are absorbed by the positive
logarithmic term of the published error. -/

namespace TwoPointCorrelations

lemma halasz_loglog_ten_pos : 0 < Real.log (Real.log (10:ℝ)) := by
  apply Real.log_pos
  have hh := Real.log_lt_log (Real.exp_pos 1)
    (show Real.exp 1 < (10:ℝ) by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using hh

lemma halasz_bounded_length_ratio {B : ℝ} (hB : 10 ≤ B) {H : ℕ}
    (hH : 10 ≤ H) (hHB : (H:ℝ) ≤ B) :
    1 ≤ (Real.log B/Real.log (Real.log (10:ℝ)))*
      (Real.log (Real.log (H:ℝ))/Real.log H) := by
  have hHr : (10:ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : 0 < (H:ℝ) := by linarith
  have hB0 : 0 < B := by linarith
  have hlH : 0 < Real.log (H:ℝ) := Real.log_pos (by linarith)
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hc := halasz_loglog_ten_pos
  have hLH : Real.log (10:ℝ) ≤ Real.log (H:ℝ) := Real.log_le_log (by norm_num) hHr
  have hLL : Real.log (Real.log (10:ℝ)) ≤ Real.log (Real.log (H:ℝ)) :=
    Real.log_le_log (Real.log_pos (by norm_num)) hLH
  have hlogHB : Real.log (H:ℝ) ≤ Real.log B := Real.log_le_log hH0 hHB
  have hr : Real.log (Real.log (10:ℝ))/Real.log B ≤
      Real.log (Real.log (H:ℝ))/Real.log H :=
    (div_le_div_of_nonneg_left hc.le hlH hlogHB).trans
      (div_le_div_of_nonneg_right hLL hlH.le)
  have hh := mul_le_mul_of_nonneg_left hr (div_pos hlB hc).le
  have he : (Real.log B/Real.log (Real.log (10:ℝ)))*
      (Real.log (Real.log (10:ℝ))/Real.log B) = 1 := by field_simp
  rwa [he] at hh

lemma halasz_short_bounded_length (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) {B : ℝ} (hB : 10 ≤ B) (hH : 10 ≤ H) (hHB : (H:ℝ) ≤ B) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (Real.log B/Real.log (Real.log (10:ℝ)))*X*H*
        (Real.log (Real.log (H:ℝ))/Real.log H) := by
  have hh := mul_le_mul_of_nonneg_right (halasz_bounded_length_ratio hB hH hHB)
    (mul_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg H) : (0:ℝ)≤X*H)
  calc
    _ ≤ (X:ℝ)*H := minor_arc_short_integral_trivial F hF X H α
    _ ≤ _ := by convert hh using 1 <;> ring

end TwoPointCorrelations

end OAI
