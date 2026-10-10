import OAI.NumberTheory.Ostmann.Preliminaries.StableSummandTails

namespace OAI

/-! # The discarded collision weight is negligible in both prime bands -/

namespace Ostmann

open Filter

theorem eventual_affine_log_le_rpow (A B d κ : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, A * Real.log T + B ≤ d * T ^ κ := by
  have hl := ((isLittleO_log_rpow_atTop hκ).const_mul_left A).bound (show 0 < d / 2 by positivity)
  have hp := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * max B 0 / d)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hl hp hT
  have hlog : A * Real.log T ≤ d / 2 * T ^ κ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Real.log_nonneg hT)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) κ)] using hl
  have hb : B ≤ d / 2 * T ^ κ := by
    have hh := (div_le_iff₀ hd).mp hp
    linarith [le_max_left B 0]
  linarith

theorem eventual_tailDefectBudget_negligible (a C δ d κ : ℝ)
    (hδ : 0 < δ) (hd : 0 < d) (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, 1 ≤ L → L ≤ 2 * T ^ 2 →
      64 * tailDefectBudget a C L / δ ^ 2 ≤ d * T ^ κ := by
  let B := 24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a
  have hh := eventual_affine_log_le_rpow (2560 / δ ^ 2) (64 * B / δ ^ 2) d κ
    (by positivity) hd hκ
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with T hh hT L hL hLT
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := by linarith
  have hlog : Real.log L ≤ Real.log 2 + 2 * Real.log T := by
    have h := Real.log_le_log hLp hLT
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hTp.ne'), Real.log_pow] at h
    exact h
  have hE : tailDefectBudget a C L ≤ 40 * Real.log T + B := by
    dsimp [tailDefectBudget, B]
    linarith
  calc
    64 * tailDefectBudget a C L / δ ^ 2 ≤ 64 * (40 * Real.log T + B) / δ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) (sq_nonneg _)
    _ = (2560 / δ ^ 2) * Real.log T + 64 * B / δ ^ 2 := by ring
    _ ≤ _ := hh

end Ostmann

end OAI
