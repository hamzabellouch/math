import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters

namespace OAI

/-! Final scale arithmetic in the qualitative rough-shift estimate. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_qualitative_frequency_gap :
    ∀ᶠ B : ℝ in atTop,
      (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ (6 : ℕ) ≤
        (B ^ (-10001 / 10000 : ℝ)) ^ (5 : ℕ) := by
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 10 : ℝ) by norm_num)).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, hs] with B hB hb
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hBp _), one_mul] at hb
  have hq : Real.log B / B ^ (9999 / 10000 : ℝ) ≤ B ^ (-8999 / 10000 : ℝ) := by
    calc
      _ ≤ B ^ (1 / 10 : ℝ) / B ^ (9999 / 10000 : ℝ) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by rw [← Real.rpow_sub hBp]; norm_num
  calc
    _ ≤ (B ^ (-8999 / 10000 : ℝ)) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hq 6
    _ = B ^ (-26997 / 5000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num
    _ ≤ B ^ (-10001 / 2000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num

lemma eventually_qualitative_interval_lower :
    ∀ᶠ B : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D → 10 ≤ D := by
  have hh := ((Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (show 0 < (9999 / 10000 : ℝ) by norm_num))).const_mul_atTop
      (show 0 < (1 / 2 : ℝ) by norm_num)).eventually (eventually_ge_atTop 10)
  filter_upwards [hh] with B hb
  intro D hD
  exact_mod_cast hb.trans hD

lemma eventually_fixed_interval_endpoint (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℕ in atTop, 0 < Y ∧ (D : ℝ) / Y ≤ η := by
  have hb : ∀ᶠ Y : ℕ in atTop, (D : ℝ) / η ≤ Y :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  filter_upwards [hb, eventually_ge_atTop 1] with Y hy hY
  refine ⟨by omega, ?_⟩
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  apply (div_le_iff₀ hYr).mpr
  have ht := (div_le_iff₀ hη).mp hy
  nlinarith only [ht]

end TwoPointCorrelations

end OAI
