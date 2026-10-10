import OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingLength
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingBand

namespace OAI

/-! Prime-band costs for the fifth-root working length. Both density
and the minor-arc fourth root have the same elementary rate. -/
namespace TwoPointCorrelations

open Filter

lemma major_arc_working_log_lower {H : ℕ} {W : ℝ}
    (hW : 1 ≤ W) (hH : 1 ≤ Real.log (H:ℝ))
    (hWH : W ≤ Real.log (H:ℝ)^5)
    (hcap : W^(1/5:ℝ)/4 ≤ Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ)) :
    W^(1/5:ℝ)/4 ≤ Real.log (majorArcWorkingLength H W:ℝ) := by
  have hW0 : 0 < W := by linarith
  have hroot : W^(1/5:ℝ) ≤ Real.log (H:ℝ) := by
    calc
      _ ≤ (Real.log (H:ℝ)^5)^(1/5:ℝ) := Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Real.log (H:ℝ))]
        norm_num
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · nlinarith [Real.rpow_nonneg hW0.le (1/5:ℝ)]
  · exact hcap

lemma major_arc_working_upper_log {H : ℕ} {W : ℝ} (hW : 2 ≤ W)
    (hpower : W^6 ≤ (majorArcWorkingLength H W:ℝ)) :
    2 ≤ (majorArcWorkingLength H W:ℝ)/W^3 ∧
    Real.log (majorArcWorkingLength H W:ℝ)/2 ≤
      Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hthird : 2 ≤ W^3 := hW.trans (le_self_pow₀ hW1 (by decide))
  have hdiv : W^3 ≤ (majorArcWorkingLength H W:ℝ)/W^3 := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    simpa only [← pow_add] using hpower
  have hpos : (0:ℝ) < majorArcWorkingLength H W := (pow_pos hW0 6).trans_le hpower
  have hl := Real.log_le_log (pow_pos hW0 6) hpower
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  refine ⟨hthird.trans hdiv,?_⟩
  rw [Real.log_div hpos.ne' (pow_ne_zero 3 hW0.ne'),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

lemma major_arc_working_band_density (A : ℕ) {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : 1 ≤ Real.log (H:ℝ))
    (hWH : W ≤ Real.log (H:ℝ)^5)
    (hpower : W^6 ≤ (majorArcWorkingLength H W:ℝ))
    (hcap : W^(1/5:ℝ)/4 ≤ Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ)) :
    Real.log (W^A)/Real.log ((majorArcWorkingLength H W:ℝ)/W^3) ≤
      8*(A:ℝ)*majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hl := major_arc_working_log_lower (by linarith : 1 ≤ W) hH hWH hcap
  have hQ := (major_arc_working_upper_log hW hpower).2
  have hlow : W^(1/5:ℝ)/8 ≤ Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  rw [Real.log_pow]
  calc
    _ ≤ ((A:ℝ)*Real.log W)/(W^(1/5:ℝ)/8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = 8*(A:ℝ)*(Real.log W*W^(-1/5:ℝ)) := by
      rw [show (-1/5:ℝ)=-(1/5:ℝ) by ring,Real.rpow_neg hW0.le]
      ring
    _ ≤ _ := by
      unfold majorArcWorkingError
      gcongr
      linarith

lemma major_arc_minor_working_rate {W h : ℝ} (hW : 1 ≤ W)
    (hh : 1 ≤ Real.log h) (hupper : Real.log h ≤ W^(1/5:ℝ)) :
    Real.log (Real.log h)*(Real.log h/W)^(1/4:ℝ) ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hlog0 : 0 < Real.log h := by linarith
  have hlog := Real.log_le_log hlog0 hupper
  rw [Real.log_rpow hW0] at hlog
  have hp : (Real.log h/W)^(1/4:ℝ) ≤ W^(-1/5:ℝ) := by
    calc
      _ ≤ (W^(1/5:ℝ)/W)^(1/4:ℝ) := Real.rpow_le_rpow
        (div_nonneg hlog0.le hW0.le) (div_le_div_of_nonneg_right hupper hW0.le) (by norm_num)
      _ = _ := by
        rw [div_eq_mul_inv,← Real.rpow_neg_one W,← Real.rpow_add hW0,← Real.rpow_mul hW0.le]
        norm_num
  unfold majorArcWorkingError
  apply mul_le_mul _ hp (Real.rpow_nonneg (div_nonneg hlog0.le hW0.le) _) (by linarith [Real.log_nonneg hW])
  nlinarith [Real.log_nonneg hW]

lemma major_arc_working_band_budget (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 10 ≤ Real.log W) (hW0 : 0 < W)
    (hQ : 1 < Q) (hQH : Q ≤ majorArcWorkingLength H W) :
    8192 * (Real.log (Real.log Q) + 1) ≤ (1 / 100 : ℝ) * Real.log (W ^ A) := by
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (show 0 ≤ Real.log W by linarith)
  rw [Real.log_pow]
  nlinarith

lemma major_arc_working_band_resolution (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 1 ≤ W) (hQ : 1 < Q)
    (hQH : Q ≤ majorArcWorkingLength H W) :
    W ^ (100 : ℕ) ≤ mrtBaseResolution (W ^ A) Q (1 / 100) := by
  have hW0 : 0 < W := by linarith
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (Real.log_nonneg hW)
  rw [show W ^ (100 : ℕ) = Real.exp ((100 : ℝ) * Real.log W) by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hW0]
    congr 1
    ring, mrtBaseResolution, Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_nonneg hW]

end TwoPointCorrelations

end OAI
