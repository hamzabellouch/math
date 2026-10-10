import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionWindowScale

namespace OAI

/-! The divisor correction preserves the numerical budgets used in the
major-arc reduction. In particular, dilation of the additive frequency
costs only a factor two in the perturbation budget. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_correction_divisor_le_window {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hdW : (d : ℝ) ≤ W ^ (5 : ℕ)) (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    d ≤ h := by
  have hW0 : 0 < W := by linarith
  have hp : W ^ (5 : ℕ) ≤ W ^ (248 : ℕ) := pow_le_pow_right₀ hW (by norm_num)
  have he : W ^ (248 : ℕ) = W ^ (250 : ℕ) / W ^ (2 : ℕ) := by
    rw [show (250 : ℕ) = 248 + 2 by decide, pow_add]
    exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
  have hle : (d : ℝ) ≤ (h : ℝ) :=
    hdW.trans (hp.trans (he.le.trans ((div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)).trans hh)))
  exact_mod_cast hle

lemma mrt_correction_quotient_volume {X h d : ℕ}
    (hd : 0 < d) (hdh : d ≤ h) (hhX : h ≤ X) :
    (d : ℝ) * (X / d + 1 : ℕ) * (h / d + 1 : ℕ) ≤
      4 * (X : ℝ) * h / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hx := mrt_quotient_length_le_two hd (hdh.trans hhX)
  have hh := mrt_quotient_length_le_two hd hdh
  calc
    _ ≤ (d : ℝ) * (2 * ((X : ℝ) / d)) * (2 * ((h : ℝ) / d)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hx hdr.le
      · exact hh
      · positivity
      · positivity
    _ = _ := by field_simp; ring

lemma mrt_correction_phase_budget {W β : ℝ} {d H q : ℕ}
    (hd : 0 < d) (hdH : d ≤ H) (hq : 0 < q)
    (hβ : |β| ≤ W / ((H : ℝ) * q)) :
    |(d : ℝ) * β| ≤ (2 * W) / ((H / d + 1 : ℕ) * (q : ℝ)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hHr : (0 : ℝ) < H := by exact_mod_cast hd.trans_le hdH
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hH' : (0 : ℝ) < (H / d + 1 : ℕ) := by positivity
  have hbase : |β| * ((H : ℝ) * q) ≤ W := (le_div_iff₀ (mul_pos hHr hqr)).mp hβ
  have hlen : (d : ℝ) * (H / d + 1 : ℕ) ≤ 2 * H := by
    calc
      _ ≤ (d : ℝ) * (2 * ((H : ℝ) / d)) :=
        mul_le_mul_of_nonneg_left (mrt_quotient_length_le_two hd hdH) hdr.le
      _ = _ := by field_simp
  apply (le_div_iff₀ (mul_pos hH' hqr)).mpr
  calc
    _ = |β| * (((d : ℝ) * (H / d + 1 : ℕ)) * q) := by
      rw [abs_mul, abs_of_pos hdr]
      ring
    _ ≤ |β| * ((2 * H) * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlen hqr.le) (abs_nonneg _)
    _ = 2 * (|β| * ((H : ℝ) * q)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by norm_num)

lemma mrt_correction_log_power_saving {W L : ℝ} (hW : 0 < W)
    (hL : W ^ (5 : ℕ) / 2 ≤ L) :
    L ^ (-(1 / 4 : ℝ)) ≤ 2 * W ^ (-(5 / 4 : ℝ)) := by
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc
    _ ≤ (W ^ (5 : ℕ) / 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hL (by norm_num)
    _ = W ^ (-(5 / 4 : ℝ)) / (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.div_rpow (pow_nonneg hW.le _) (by norm_num), mrt_correction_fifth_tail hW.le]
    _ ≤ _ := by
      apply (div_le_iff₀ htwo).mpr
      nlinarith [Real.rpow_nonneg hW.le (-(5 / 4 : ℝ))]

/-- The outer logarithmic error in the typical mean is smaller than the
required correction scale, uniformly over all small correction divisors. -/
theorem mrt_correction_outer_saving :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ W ^ (5 : ℕ) →
        (Real.log (X / d + 1 : ℕ)) ^ (-(1 / 4 : ℝ)) ≤
          2 * W ^ (-(5 / 4 : ℝ)) ∧ (X : ℝ) ≤ ((X / d + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
  filter_upwards [mrt_correction_outer_log_scale, eventually_ge_atTop (1 : ℕ)] with X hs hX
  intro W hW hWX d hd hdW
  obtain ⟨hlo, _⟩ := hs.2 W hW hWX d hd hdW
  have hW0 : 0 < W := by linarith
  have hL0 : 0 < Real.log (X : ℝ) := by linarith [hs.1]
  have hpow : W ^ (5 : ℕ) ≤ Real.log (X : ℝ) := by
    calc
      _ ≤ ((Real.log (X : ℝ)) ^ (1 / 125 : ℝ)) ^ (5 : ℕ) :=
        pow_le_pow_left₀ hW0.le hWX 5
      _ = (Real.log (X : ℝ)) ^ (1 / 25 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ Real.log (X : ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show 1 ≤ Real.log (X : ℝ) by linarith [hs.1]) (show (1 / 25 : ℝ) ≤ 1 by norm_num)
  refine ⟨mrt_correction_log_power_saving hW0 ((div_le_div_of_nonneg_right hpow (by norm_num)).trans hlo), ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hq0 : (0 : ℝ) < (X / d + 1 : ℕ) := by positivity
  apply (Real.log_le_log_iff hX0 (pow_pos hq0 2)).mp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

end TwoPointCorrelations

end OAI
