import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Characters.PivotTargetScale

namespace OAI

/-! # The prescribed gaps are small compared with the top-prime scale -/

namespace Ostmann

open Filter

noncomputable def characterBaseGap (B z m : ℝ) : ℝ := (B + 20 * Real.log z) * m

/-- The index is zero based here; this is the manuscript's `Delta_(i+1)`. -/
noncomputable def characterPivotGap (B z m : ℝ) (i : ℕ) : ℝ :=
  (2 : ℝ) ^ i * characterBaseGap B z m + (4 : ℝ) ^ (i + 1) * Real.sqrt m

theorem eventual_character_target_gaps (k : ℕ) (B z α : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m τ : ℝ, 0 ≤ m → m ≤ z * L → Real.exp (α * L) ≤ τ →
      0 ≤ characterBaseGap B z m ∧ characterBaseGap B z m ≤ τ / 4 ∧
      ∀ i < k, 0 ≤ characterPivotGap B z m i ∧
        characterPivotGap B z m i ≤ (2 : ℝ) ^ i * τ / 4 := by
  let D := B + 20 * Real.log z
  let C := (2 : ℝ) ^ k * D + (4 : ℝ) ^ (k + 1)
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h4 : (0 : ℝ) ≤ 4 ^ (k + 1) := by positivity
    have h := mul_le_mul_of_nonneg_right h2 hD
    dsimp [C]
    linarith
  have hp := (isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left (4 * C * z)
  have hc := (isLittleO_pow_exp_pos_mul_atTop 0 hα).const_mul_left (4 * C)
  have hb := (hp.add hc).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hlarge hL m τ hm hmL hτ
  have hlarge' : 4 * C * (z * L + 1) ≤ τ := by
    have hbound := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one, pow_zero, mul_one, one_mul]
        using hlarge)
    nlinarith only [hbound, hτ]
  have hbase : characterBaseGap B z m ≤ C * (z * L + 1) := by
    change D * m ≤ _
    have h1 := mul_le_mul_of_nonneg_right hDC hm
    have h2 := mul_le_mul_of_nonneg_left hmL hC
    nlinarith
  have hτpos : 0 < τ := (Real.exp_pos _).trans_le hτ
  refine ⟨mul_nonneg hD hm, by linarith, ?_⟩
  intro i hi
  have hi2 : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi.le
  have hi4 : (4 : ℝ) ^ (i + 1) ≤ 4 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsqrt : Real.sqrt m ≤ m + 1 := by
    have hs := Real.sq_sqrt hm
    have hn := Real.sqrt_nonneg m
    nlinarith [sq_nonneg (Real.sqrt m - 1)]
  have hgap : characterPivotGap B z m i ≤ C * (m + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hi2 (mul_nonneg hD hm)
    have h2 := mul_le_mul hi4 hsqrt (Real.sqrt_nonneg m) (by positivity : (0 : ℝ) ≤ 4 ^ (k + 1))
    change (2 : ℝ) ^ i * (D * m) + (4 : ℝ) ^ (i + 1) * Real.sqrt m ≤
      ((2 : ℝ) ^ k * D + (4 : ℝ) ^ (k + 1)) * (m + 1)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 ^ k by positivity) hD]
  have hgap' : characterPivotGap B z m i ≤ τ / 4 := by
    have h := mul_le_mul_of_nonneg_left hmL hC
    linarith
  have hpow : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hscale := mul_le_mul_of_nonneg_right hpow hτpos.le
  refine ⟨by dsimp [characterPivotGap, characterBaseGap]; positivity, ?_⟩
  nlinarith

end Ostmann

end OAI
