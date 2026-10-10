import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionArcScale

namespace OAI

/-! Scalar rates for a square-root modulus loss and the elementary
q^(1/100) divisor bound. These estimates do not assume or prove the
analytic character-resolution inequality. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_sqrt_modulus_power {W : ℝ} (hW : 0 < W) :
    Real.sqrt W * W ^ (1 / 100 : ℝ) = W ^ (51 / 100 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW]
  norm_num

theorem mrt_sqrt_modulus_log_saving :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ L ^ (1 / 170 : ℝ) →
      Real.sqrt W * W ^ (1 / 100 : ℝ) *
        Real.sqrt (Real.log L / L ^ (1 / 100 : ℝ)) ≤ L ^ (-(1 / 700 : ℝ)) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 1000 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with L hs hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hp : 0 ≤ L ^ (1 / 1000 : ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg hp, one_mul] at hs
  intro W hW hWL
  have hW0 : 0 < W := by linarith
  have hmod : Real.sqrt W * W ^ (1 / 100 : ℝ) ≤ L ^ (3 / 1000 : ℝ) := by
    rw [mrt_sqrt_modulus_power hW0]
    calc
      _ ≤ (L ^ (1 / 170 : ℝ)) ^ (51 / 100 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWL (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hL0.le]; norm_num
  have hratio : Real.log L / L ^ (1 / 100 : ℝ) ≤ L ^ (-(9 / 1000 : ℝ)) := by
    calc
      _ ≤ L ^ (1 / 1000 : ℝ) / L ^ (1 / 100 : ℝ) :=
        div_le_div_of_nonneg_right hs (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_sub hL0]; norm_num
  have hsqrt : Real.sqrt (Real.log L / L ^ (1 / 100 : ℝ)) ≤
      L ^ (-(9 / 2000 : ℝ)) := by
    calc
      _ ≤ Real.sqrt (L ^ (-(9 / 1000 : ℝ))) := Real.sqrt_le_sqrt hratio
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]; norm_num
  calc
    _ ≤ L ^ (3 / 1000 : ℝ) * L ^ (-(9 / 2000 : ℝ)) :=
      mul_le_mul hmod hsqrt (Real.sqrt_nonneg _) (Real.rpow_nonneg hL0.le _)
    _ = L ^ (-(3 / 2000 : ℝ)) := by rw [← Real.rpow_add hL0]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

lemma mrt_arc_outer_quarter {L : ℝ} (hL : 1 ≤ L) :
    (L ^ (1 / 170 : ℝ)) ^ (-(1 / 4 : ℝ)) ≤ L ^ (-(1 / 700 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.rpow_mul hL0.le]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

lemma mrt_arc_short_quarter {H : ℝ} (hlog : 1 ≤ Real.log H)
    (hloglog : 1 ≤ Real.log (Real.log H)) :
    ((Real.log H) ^ (5 : ℕ)) ^ (-(1 / 4 : ℝ)) ≤
      Real.log (Real.log H) / Real.log H := by
  have hL0 : 0 < Real.log H := by linarith
  rw [mrt_correction_fifth_tail hL0.le]
  calc
    _ ≤ (Real.log H) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
    _ = 1 / Real.log H := by rw [Real.rpow_neg_one]; simp only [one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hloglog hL0.le

lemma mrt_arc_exp_quarter (M : ℝ) :
    (Real.exp (M / 5)) ^ (-(1 / 4 : ℝ)) = Real.exp (-M / 20) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

lemma mrt_arc_exp_modulus {W M : ℝ} (hW : 0 < W) (hM : 0 ≤ M)
    (hWM : W ≤ Real.exp (M / 5)) :
    Real.sqrt W * W ^ (1 / 100 : ℝ) * Real.exp (-M / 5) ≤ Real.exp (-M / 20) := by
  rw [mrt_sqrt_modulus_power hW]
  calc
    _ ≤ (Real.exp (M / 5)) ^ (51 / 100 : ℝ) * Real.exp (-M / 5) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hW.le hWM (by norm_num)) (Real.exp_pos _).le
    _ = Real.exp (-(49 / 500 : ℝ) * M) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

noncomputable def mrtArcParameter (L H M : ℝ) : ℝ :=
  min ((Real.log H) ^ (5 : ℕ)) (min (L ^ (1 / 170 : ℝ)) (Real.exp (M / 5)))

lemma mrt_min_rpow_le_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℝ) :
    (min a b) ^ s ≤ a ^ s + b ^ s := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)
  · rw [min_eq_right hba]
    exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)

lemma mrt_arc_parameter_bounds {L H M : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log H) (hM : 0 ≤ M) :
    1 ≤ mrtArcParameter L H M ∧
      mrtArcParameter L H M ≤ (Real.log H) ^ (5 : ℕ) ∧
      mrtArcParameter L H M ≤ L ^ (1 / 170 : ℝ) ∧
      mrtArcParameter L H M ≤ Real.exp (M / 5) := by
  have ha : 1 ≤ (Real.log H) ^ (5 : ℕ) := one_le_pow₀ hlog
  have hb : 1 ≤ L ^ (1 / 170 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hc : 1 ≤ Real.exp (M / 5) := Real.one_le_exp (by positivity)
  exact ⟨le_min ha (le_min hb hc), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

lemma mrt_arc_parameter_quarter {L H M : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log H) (hloglog : 1 ≤ Real.log (Real.log H)) :
    (mrtArcParameter L H M) ^ (-(1 / 4 : ℝ)) ≤
      Real.log (Real.log H) / Real.log H + L ^ (-(1 / 700 : ℝ)) + Real.exp (-M / 20) := by
  have hA : 0 ≤ (Real.log H) ^ (5 : ℕ) := pow_nonneg (by linarith) _
  have hB : 0 ≤ L ^ (1 / 170 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hC : 0 ≤ Real.exp (M / 5) := (Real.exp_pos _).le
  have hh := mrt_min_rpow_le_sum hA (le_min hB hC) (-(1 / 4 : ℝ))
  have hi := mrt_min_rpow_le_sum hB hC (-(1 / 4 : ℝ))
  change (min ((Real.log H) ^ (5 : ℕ)) (min (L ^ (1 / 170 : ℝ)) (Real.exp (M / 5)))) ^
    (-(1 / 4 : ℝ)) ≤ _
  have ht := mrt_arc_short_quarter hlog hloglog
  have hl := mrt_arc_outer_quarter hL
  rw [mrt_arc_exp_quarter] at hi
  linarith

end TwoPointCorrelations

end OAI
