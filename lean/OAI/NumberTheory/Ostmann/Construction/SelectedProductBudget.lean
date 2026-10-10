import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationFrequency

namespace OAI

/-! # The actual tail-cell errors fit both numerical transfer reserves -/
namespace Ostmann
open Filter

theorem eventual_tailDefectBudget_nonneg (a C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → 0 ≤ tailDefectBudget a C X := by
  let K := 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a
  filter_upwards [eventually_ge_atTop (-5 * K / 4)] with L hL X hX
  have hx : 0 < X := (Real.exp_pos _).trans_le hX
  have hl := (Real.le_log_iff_exp_le hx).mpr hX
  dsimp only [tailDefectBudget, K] at *
  linarith

theorem eventual_selected_product_budgets (a C : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hfreq : 2 * (704 * tailCellLinearRate a C + 26) ≤ (k : ℝ) ^ 3)
    (hrigid : 80 * (256 * tailCellLinearRate a C + 9) ≤ (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      0 ≤ tailDefectBudget a C X ∧
      256 * tailDefectBudget a C X + 9 ≤ (spectatorBulkCount k L : ℝ) / 40 ∧
      ∀ n ≤ k,
        (6 + 4 * k) * (64 * tailDefectBudget a C X + 1) +
          2 * ((3 + 2 * k : ℕ) + 3) + n * (256 * tailDefectBudget a C X + 9) ≤
            (spectatorBulkCount k L : ℝ) := by
  filter_upwards [eventual_tailDefectBudget_nonneg a C, eventually_ge_atTop (1 : ℝ)]
    with L hD hL X hXlo hXhi
  have hx : 0 < X := (Real.exp_pos _).trans_le hXlo
  have hD0 := hD X hXlo
  have hDhi := tailDefectBudget_linear a C L X hL hx hXhi
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk4 : (2 : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hk2 4
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ (k : ℝ) ^ 4 by positivity)]
  have hhalf := spectatorBulkCount_half k L hscale
  refine ⟨hD0, ?_, fun n hn => ?_⟩
  · have he : 256 * tailDefectBudget a C X + 9 ≤
        (256 * tailCellLinearRate a C + 9) * L := by nlinarith only [hDhi, hL]
    have hs := mul_le_mul_of_nonneg_right hrigid (show 0 ≤ L by linarith)
    nlinarith only [he, hs, hhalf]
  · exact moving_cell_frequency_rounding_budget k n (tailCellLinearRate a C)
      (tailDefectBudget a C X) L hk hn hD0 hL hDhi hfreq hscale

end Ostmann

end OAI
