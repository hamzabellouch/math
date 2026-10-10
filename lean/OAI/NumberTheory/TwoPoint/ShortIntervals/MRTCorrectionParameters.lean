import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionQuotient

namespace OAI

/-! Scalar budgets for the prime-power correction. The real parameter W
allows the published logarithmic cutoff, while the actual divisor cutoff
is the natural floor of W^5. -/

namespace TwoPointCorrelations

open scoped Classical

noncomputable def mrtCorrectionCutoff (W : ℝ) : ℕ := ⌊W ^ (5 : ℕ)⌋₊

lemma mrt_correction_fifth_tail {W : ℝ} (hW : 0 ≤ W) :
    (W ^ (5 : ℕ)) ^ (-(1 / 4 : ℝ)) = W ^ (-(5 / 4 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  norm_num

lemma mrt_correction_endpoint {W H : ℝ} (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H) :
    W ^ (5 : ℕ) / H ≤ W ^ (-(5 / 4 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 250).trans_le hH
  apply (div_le_iff₀ hH0).mpr
  calc
    W ^ (5 : ℕ) = W ^ (-(5 / 4 : ℝ)) * W ^ (25 / 4 : ℝ) := by
      rw [← Real.rpow_add hW0]
      norm_num
    _ ≤ W ^ (-(5 / 4 : ℝ)) * W ^ (250 : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hW0.le _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hW0.le _)

lemma mrt_correction_cutoff_bounds {W : ℝ} (hW : 2 ≤ W) :
    1 ≤ mrtCorrectionCutoff W ∧
      W ^ (5 : ℕ) / 2 ≤ (mrtCorrectionCutoff W : ℝ) ∧
      (mrtCorrectionCutoff W : ℝ) ≤ W ^ (5 : ℕ) := by
  have hW1 : 1 ≤ W := by linarith
  have hpow : 2 ≤ W ^ (5 : ℕ) :=
    hW.trans (le_self_pow₀ hW1 (by norm_num : (5 : ℕ) ≠ 0))
  have hlt := Nat.lt_floor_add_one (W ^ (5 : ℕ))
  refine ⟨?_, ?_, Nat.floor_le (pow_nonneg (by linarith) _)⟩
  · exact (Nat.one_le_floor_iff _).mpr (by linarith)
  · change W ^ (5 : ℕ) / 2 ≤ (⌊W ^ (5 : ℕ)⌋₊ : ℝ)
    linarith

lemma mrt_correction_cutoff_tail {W : ℝ} (hW : 2 ≤ W) :
    (mrtCorrectionCutoff W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * W ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨_, hlo, _⟩ := mrt_correction_cutoff_bounds hW
  have hW0 : 0 < W := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ (W ^ (5 : ℕ) / 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)
    _ = W ^ (-(5 / 4 : ℝ)) / (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.div_rpow (pow_nonneg hW0.le _) (by norm_num), mrt_correction_fifth_tail hW0.le]
    _ ≤ _ := by
      apply (div_le_iff₀ htwo).mpr
      nlinarith [Real.rpow_nonneg hW0.le (-(5 / 4 : ℝ))]

lemma mrt_correction_cutoff_scale {W : ℝ} {H : ℕ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    0 < mrtCorrectionCutoff W ∧ mrtCorrectionCutoff W ≤ H ∧
      (mrtCorrectionCutoff W : ℝ) / H ≤ W ^ (-(5 / 4 : ℝ)) ∧
      (mrtCorrectionCutoff W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * W ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨hpos, _, hupper⟩ := mrt_correction_cutoff_bounds hW
  have hW1 : 1 ≤ W := by linarith
  have hpow : W ^ (5 : ℕ) ≤ W ^ (250 : ℕ) :=
    pow_le_pow_right₀ hW1 (by norm_num)
  have hH0 : (0 : ℝ) < H := (pow_pos (by linarith : 0 < W) 250).trans_le hH
  refine ⟨by omega, ?_, ?_, mrt_correction_cutoff_tail hW⟩
  · exact_mod_cast hupper.trans (hpow.trans hH)
  · exact (div_le_div_of_nonneg_right hupper hH0.le).trans (mrt_correction_endpoint hW1 hH)

lemma mrt_correction_quotient_length {W H : ℝ} {h d : ℕ}
    (hW : 0 < W) (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    H / W ^ (7 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : (h : ℝ) / d < (h / d + 1 : ℕ) := by
    apply (div_lt_iff₀ hdr).mpr
    have ht : (h : ℝ) < (d : ℝ) * (h / d + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ h hd
    simpa only [mul_comm] using ht
  calc
    H / W ^ (7 : ℕ) = (H / W ^ (2 : ℕ)) / W ^ (5 : ℕ) := by
      rw [div_div, ← pow_add]
    _ ≤ (h : ℝ) / W ^ (5 : ℕ) := div_le_div_of_nonneg_right hh (pow_nonneg hW.le _)
    _ ≤ (h : ℝ) / d := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdr hdW
    _ ≤ _ := hquot.le

lemma mrt_correction_quotient_power {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    W ^ (243 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  calc
    W ^ (243 : ℕ) = W ^ (250 : ℕ) / W ^ (7 : ℕ) := by
      rw [show (250 : ℕ) = 243 + 7 by decide, pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H / W ^ (7 : ℕ) := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_correction_quotient_length hW0 hd hdW hh

end TwoPointCorrelations

end OAI
