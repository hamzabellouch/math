import OAI.NumberTheory.Ostmann.Construction.ScheduledCoefficientGap

namespace OAI

/-! # The remaining scalar reserves for the selected finite iteration -/
namespace Ostmann
open Filter

theorem eventual_scheduled_iteration_thresholds (k : ℕ) (hk : 2 ≤ k) (a C : ℝ)
    (hklarge : 20480 * tailCellLinearRate a C + 720 ≤ (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, 0 < Y → Y ≤ Real.exp L →
      ∀ (top : ℕ) (cs : List ℕ), cs.length = k →
      256 ≤ (spectatorBulkCount k L : ℝ) ∧
      (8 + 4 * cs.length : ℕ) ≤ L ∧
      256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40 ∧
      40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
        20 * Real.log 2 < (spectatorBulkCount k L : ℝ) := by
  have hkt : 0 < k := by omega
  have hm := spectatorBulkCount_tendsto k hkt
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((8 + 4 * k : ℕ) : ℝ),
    hm.eventually (eventually_ge_atTop (256 : ℝ)),
    hm.eventually (eventually_gt_atTop (40 * (2 * ((3 + 2 * k : ℕ) + 3) + 14 + 4 * k) +
      20 * Real.log 2))] with L hL hcount hmass hround
  intro Y hY hYupper top cs hlen
  have hR := tailCellLinearRate_nonneg a C
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      exact hh
    nlinarith only [hk4, hL]
  have hhalf := spectatorBulkCount_half k L hscale
  have hdef := tailDefectBudget_linear a C L Y hL hY hYupper
  have hlinear := mul_le_mul_of_nonneg_right hklarge (show 0 ≤ L by linarith)
  refine ⟨hmass, ?_, ?_, ?_⟩
  · simpa only [hlen] using hcount
  · nlinarith only [hlinear, hhalf, hdef, hL]
  · simpa only [initialSmallCellList_length, hlen] using hround

end Ostmann

end OAI
