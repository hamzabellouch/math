import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Dividing by the small correction factors preserves the logarithmic
short-window and outer-scale rates. All floor quotients remain literal. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_correction_window_log_lower {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    (243 / 250 : ℝ) * Real.log H ≤ Real.log (h / d + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 250).trans_le hH
  have hpower := Real.log_le_log (pow_pos hW0 250) hH
  rw [Real.log_pow] at hpower
  norm_num only [Nat.cast_ofNat] at hpower
  have hquot := mrt_correction_quotient_length hW0 hd hdW hh
  have hlog := Real.log_le_log (div_pos hH0 (pow_pos hW0 7)) hquot
  rw [Real.log_div hH0.ne' (pow_ne_zero 7 hW0.ne'), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

lemma mrt_loglog_ratio_of_comparable {H y : ℝ} (_hH0 : 0 < H)
    (_hy0 : 0 < y) (hlogH : 2 ≤ Real.log H)
    (hlo : Real.log H / 2 ≤ Real.log y) (hhi : Real.log y ≤ 2 * Real.log H) :
    Real.log (Real.log y) / Real.log y ≤
      4 * Real.log (Real.log H) / Real.log H := by
  have hLH0 : 0 < Real.log H := by linarith
  have hLy0 : 0 < Real.log y := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log H) := Real.log_nonneg (by linarith)
  have hlogtwo : Real.log 2 ≤ Real.log (Real.log H) :=
    Real.log_le_log (by norm_num) hlogH
  have hLL := Real.log_le_log hLy0 hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLH0.ne'] at hLL
  have hLLhi : Real.log (Real.log y) ≤ 2 * Real.log (Real.log H) := by linarith
  calc
    _ ≤ (2 * Real.log (Real.log H)) / Real.log y :=
      div_le_div_of_nonneg_right hLLhi hLy0.le
    _ ≤ (2 * Real.log (Real.log H)) / (Real.log H / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
    _ = _ := by ring

theorem mrt_correction_window_log_rate {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H) (hlogH : 2 ≤ Real.log H)
    (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) (hhH : (h : ℝ) ≤ H) :
    Real.log (Real.log (h / d + 1 : ℕ)) / Real.log (h / d + 1 : ℕ) ≤
      4 * Real.log (Real.log H) / Real.log H := by
  have hH0 : 0 < H := (pow_pos (by linarith : 0 < W) 250).trans_le hH
  have hq0 : (0 : ℝ) < (h / d + 1 : ℕ) := by positivity
  have hlo := mrt_correction_window_log_lower hW hH hd hdW hh
  have hL0 : 0 ≤ Real.log H := by linarith
  have hlo' : Real.log H / 2 ≤ Real.log (h / d + 1 : ℕ) := by nlinarith
  have hq : (h / d + 1 : ℕ) ≤ h + 1 := Nat.add_le_add_right (Nat.div_le_self h d) 1
  have hqr : ((h / d + 1 : ℕ) : ℝ) ≤ H + 1 := by
    have hr : ((h / d + 1 : ℕ) : ℝ) ≤ (h : ℝ) + 1 := by exact_mod_cast hq
    linarith
  have hH2 : 2 ≤ H := by linarith [Real.log_le_sub_one_of_pos hH0]
  have hqH : ((h / d + 1 : ℕ) : ℝ) ≤ H ^ 2 := by nlinarith
  have hhi := Real.log_le_log hq0 hqH
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  exact mrt_loglog_ratio_of_comparable hH0 hq0 hlogH hlo' hhi

/-- The published modulus-size bound keeps each corrected outer cutoff
within a fixed logarithmic factor of the original cutoff. -/
theorem mrt_correction_outer_log_scale :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X : ℝ) ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ W ^ (5 : ℕ) →
        Real.log (X : ℝ) / 2 ≤ Real.log (X / d + 1 : ℕ) ∧
        Real.log (X / d + 1 : ℕ) ≤ 2 * Real.log (X : ℝ) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hscale : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (2 : ℕ) ≤ (X : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall] with X hs
    dsimp only [id] at hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (X : ℝ))),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X), one_mul] at hs
    exact hs
  have hlogs : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hscale, hlogs, eventually_ge_atTop (2 : ℕ)] with X hs hL hX
  refine ⟨hL, ?_⟩
  intro W hW hWX d hd hdW
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log (X : ℝ) := by linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hWpow : W ^ (5 : ℕ) ≤ (Real.log (X : ℝ)) ^ (1 / 25 : ℝ) := by
    calc
      _ ≤ ((Real.log (X : ℝ)) ^ (1 / 125 : ℝ)) ^ (5 : ℕ) :=
        pow_le_pow_left₀ (by linarith) hWX 5
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        norm_num
  have hdL : (d : ℝ) ≤ Real.log (X : ℝ) := by
    apply hdW.trans (hWpow.trans _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ Real.log (X : ℝ) by linarith) (show (1 / 25 : ℝ) ≤ 1 by norm_num)
  have hdX : (d : ℝ) ^ 2 ≤ X := (pow_le_pow_left₀ hdr.le hdL 2).trans hs
  have hlogd := Real.log_le_log (pow_pos hdr 2) hdX
  rw [Real.log_pow] at hlogd
  norm_num only [Nat.cast_ofNat] at hlogd
  have hquot : (X : ℝ) / d < (X / d + 1 : ℕ) := by
    apply (div_lt_iff₀ hdr).mpr
    have hnat : (X : ℝ) < (d : ℝ) * (X / d + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ X hd
    simpa only [mul_comm] using hnat
  have hlo := Real.log_le_log (div_pos hX0 hdr) hquot.le
  rw [Real.log_div hX0.ne' hdr.ne'] at hlo
  have hq0 : (0 : ℝ) < (X / d + 1 : ℕ) := by positivity
  have hqX : ((X / d + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ 2 := by
    have hnat := Nat.add_le_add_right (Nat.div_le_self X d) 1
    have hreal : ((X / d + 1 : ℕ) : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast hnat
    have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hhi := Real.log_le_log hq0 hqX
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  exact ⟨by linarith, hhi⟩

end TwoPointCorrelations

end OAI
