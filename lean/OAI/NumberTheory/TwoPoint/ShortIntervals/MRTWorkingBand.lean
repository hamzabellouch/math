import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingLength
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTResolution

namespace OAI

/-! First-band parameter bounds for the piecewise working length. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_working_upper_log {H : ℕ} {W : ℝ} (hW : 2 ≤ W)
    (hpower : W ^ (6 : ℕ) ≤ (mrtWorkingLength H W : ℝ)) :
    2 ≤ (mrtWorkingLength H W : ℝ) / W ^ (3 : ℕ) ∧
      Real.log (mrtWorkingLength H W : ℝ) / 2 ≤
        Real.log ((mrtWorkingLength H W : ℝ) / W ^ (3 : ℕ)) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hthird : 2 ≤ W ^ (3 : ℕ) :=
    hW.trans (le_self_pow₀ hW1 (by decide))
  have hthirdQ : W ^ (3 : ℕ) ≤ (mrtWorkingLength H W : ℝ) / W ^ (3 : ℕ) := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    simpa only [← pow_add] using hpower
  have hh0 : (0 : ℝ) < mrtWorkingLength H W :=
    (pow_pos hW0 6).trans_le hpower
  have hlog := Real.log_le_log (pow_pos hW0 6) hpower
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  refine ⟨hthird.trans hthirdQ, ?_⟩
  rw [Real.log_div hh0.ne' (pow_ne_zero 3 hW0.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

lemma mrt_working_band_budget (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 10 ≤ Real.log W) (hW0 : 0 < W)
    (hQ : 1 < Q) (hQH : Q ≤ mrtWorkingLength H W) :
    8192 * (Real.log (Real.log Q) + 1) ≤ (1 / 100 : ℝ) * Real.log (W ^ A) := by
  have hh : (1 : ℝ) < mrtWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (mrt_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (show 0 ≤ Real.log W by linarith)
  rw [Real.log_pow]
  nlinarith

lemma mrt_working_band_resolution (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 1 ≤ W) (hQ : 1 < Q)
    (hQH : Q ≤ mrtWorkingLength H W) :
    W ^ (100 : ℕ) ≤ mrtBaseResolution (W ^ A) Q (1 / 100) := by
  have hW0 : 0 < W := by linarith
  have hh : (1 : ℝ) < mrtWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (mrt_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (Real.log_nonneg hW)
  rw [show W ^ (100 : ℕ) = Real.exp ((100 : ℝ) * Real.log W) by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hW0]
    congr 1
    ring, mrtBaseResolution, Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_nonneg hW]

/-- The density cost is bounded by the original logarithmic length term
or, on the capped branch, by W^(-1/4). -/
lemma mrt_working_band_density (A : ℕ) {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hLH : 1 ≤ Real.log (H : ℝ))
    (hWH : W ≤ (Real.log (H : ℝ)) ^ (5 : ℕ))
    (hpower : W ^ (6 : ℕ) ≤ (mrtWorkingLength H W : ℝ))
    (hcap : Real.sqrt W / 4 ≤ Real.log (mrtWorkingCap W : ℝ))
    (hsmall : Real.log W ≤ W ^ (1 / 4 : ℝ)) :
    Real.log (W ^ A) / Real.log ((mrtWorkingLength H W : ℝ) / W ^ (3 : ℕ)) ≤
      10 * (A : ℝ) * (Real.log (Real.log (H : ℝ)) / Real.log H +
        W ^ (-(1 / 4 : ℝ))) := by
  have hW0 : 0 < W := by linarith
  have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  obtain ⟨hQ, hlogQ⟩ := mrt_working_upper_log hW hpower
  have hLL : 0 ≤ Real.log (Real.log (H : ℝ)) := Real.log_nonneg hLH
  have hR : 0 ≤ Real.log (Real.log (H : ℝ)) / Real.log H :=
    div_nonneg hLL (by linarith)
  have htail : 0 ≤ W ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hW0.le _
  rw [Real.log_pow]
  by_cases hcut : (H : ℝ) ≤ Real.exp (Real.sqrt W)
  · have heq : mrtWorkingLength H W = H := by simp [mrtWorkingLength, hcut]
    rw [heq] at hlogQ ⊢
    have hwlog := Real.log_le_log hW0 hWH
    rw [Real.log_pow] at hwlog
    norm_num only [Nat.cast_ofNat] at hwlog
    calc
      _ ≤ ((A : ℝ) * Real.log W) / (Real.log H / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hA0 (Real.log_nonneg (by linarith)))
          (by linarith) hlogQ
      _ = (2 * (A : ℝ) * Real.log W) / Real.log H := by ring
      _ ≤ (10 * (A : ℝ) * Real.log (Real.log (H : ℝ))) / Real.log H := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left hwlog hA0]
      _ = 10 * (A : ℝ) * (Real.log (Real.log (H : ℝ)) / Real.log H) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail) (by positivity)
  · have heq : mrtWorkingLength H W = mrtWorkingCap W := by simp [mrtWorkingLength, hcut]
    rw [heq] at hlogQ ⊢
    have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
    have hlo : Real.sqrt W / 8 ≤
        Real.log ((mrtWorkingCap W : ℝ) / W ^ (3 : ℕ)) := by linarith
    calc
      _ ≤ ((A : ℝ) * Real.log W) / (Real.sqrt W / 8) :=
        div_le_div_of_nonneg_left (mul_nonneg hA0 (Real.log_nonneg (by linarith)))
          (by positivity) hlo
      _ ≤ ((A : ℝ) * W ^ (1 / 4 : ℝ)) / (Real.sqrt W / 8) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hA0) (by positivity)
      _ = 8 * (A : ℝ) * W ^ (-(1 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        have he : W ^ (1 / 4 : ℝ) / W ^ (1 / 2 : ℝ) = W ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_sub hW0]
          norm_num
        calc
          _ = 8 * (A : ℝ) * (W ^ (1 / 4 : ℝ) / W ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := by nlinarith [mul_nonneg hA0 hR, mul_nonneg hA0 htail]

end TwoPointCorrelations

end OAI
