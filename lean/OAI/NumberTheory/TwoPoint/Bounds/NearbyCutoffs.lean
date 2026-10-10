import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! A bounded positive-prefix mean changes little when the real cutoff
is moved within one logarithmic bin. -/

namespace TwoPointCorrelations

open Finset

lemma positivePrefix_sub_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    (N M : ℕ) (hNM : N ≤ M) :
    ‖positivePrefix f M - positivePrefix f N‖ ≤ (M - N : ℕ) := by
  have he : positivePrefix f M = positivePrefix f N +
      positivePrefix (fun n => f (N + n)) (M - N) := by
    unfold positivePrefix
    have hs := sum_range_add (fun n => f (n + 1)) N (M - N)
    rw [Nat.add_sub_of_le hNM] at hs
    simpa only [Nat.add_assoc] using hs
  rw [he, add_sub_cancel_left]
  simpa only [mul_one] using norm_positivePrefix_le (fun n => f (N + n)) (M - N) 1
    (fun n hn => hf _ (by omega))

lemma real_prefix_nearby (f : ℕ → ℂ) (hf : OneBounded f) (X Y : ℝ)
    (hY : 0 < Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * (X - Y) / X + 1 / X := by
  have hX : 0 < X := hY.trans_le hYX
  have hNM : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hYX
  have hN : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le hY.le
  have hM : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX.le
  have hlow := Nat.lt_floor_add_one Y
  have hdiff : ((⌊X⌋₊ - ⌊Y⌋₊ : ℕ) : ℝ) ≤ X - Y + 1 := by
    rw [Nat.cast_sub hNM]
    linarith
  have hnormN : ‖positivePrefix f ⌊Y⌋₊‖ ≤ (⌊Y⌋₊ : ℝ) := by
    simpa only [mul_one] using norm_positivePrefix_le f ⌊Y⌋₊ 1 hf
  have hnorm : ‖positivePrefix f ⌊Y⌋₊‖ ≤ Y := hnormN.trans hN
  have hinv : 0 ≤ 1 / Y - 1 / X := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hY hYX)
  have he : positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ) =
      positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ)) -
        (positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ))‖ +
        ‖(positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ)‖ := norm_sub_le _ _
    _ = ‖positivePrefix f ⌊Y⌋₊‖ * (1 / Y - 1 / X) +
        ‖positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊‖ / X := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hinv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    _ ≤ Y * (1 / Y - 1 / X) + (X - Y + 1) / X := by
      exact add_le_add (mul_le_mul_of_nonneg_right hnorm hinv)
        (div_le_div_of_nonneg_right
          ((positivePrefix_sub_norm_le f hf _ _ hNM).trans hdiff) hX.le)
    _ = _ := by field_simp; ring

lemma real_prefix_log_bin (f : ℕ → ℂ) (hf : OneBounded f) (X Y η : ℝ)
    (hX : 0 < X) (_hη : 0 ≤ η) (hYlow : X * Real.exp (-η) ≤ Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * η + 1 / X := by
  have hY : 0 < Y := (mul_pos hX (Real.exp_pos _)).trans_le hYlow
  apply (real_prefix_nearby f hf X Y hY hYX).trans
  have hexp : 1 - η ≤ Real.exp (-η) := by
    have he := Real.add_one_le_exp (-η)
    linarith
  have hy : X - Y ≤ X * η := by nlinarith
  have hd : (X - Y) / X ≤ η := (div_le_iff₀ hX).mpr (by nlinarith)
  calc
    _ = 2 * ((X - Y) / X) + 1 / X := by ring
    _ ≤ _ := by linarith

end TwoPointCorrelations

end OAI
