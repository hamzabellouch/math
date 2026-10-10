import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyBudget
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # From the prescribed cell sums to the diagonal's scalar gap -/

namespace Ostmann
open Filter

theorem spectatorStepGap_sub_one (BD Bz z r m : ℝ) :
    spectatorStepGap (BD - 1) Bz z r m = spectatorStepGap BD Bz z r m - r * m := by
  unfold spectatorStepGap
  ring

/-- `J + tail` is the protected and surviving compensation target in (7.4).
The two cell errors are paid by one unit of the coefficient of the step gap. -/
theorem moving_cell_diagonal_gap (BD Bz z r m J tail w b cb small cg ec es : ℝ)
    (hr : 0 ≤ r)
    (hbalance : r * w = r * (J + tail) - spectatorStepGap BD Bz z r m)
    (hupper : 4 * b ≤ w + ec)
    (hlower : r * (J + tail) - es * r ≤ small + r * (cb - 1))
    (hcost : 2 * cg + 1 + (ec + es) * r ≤ r * m) :
    2 * cg + 1 + (r * 4) * b - (small + r * (cb - 1)) ≤
      -spectatorStepGap (BD - 1) Bz z r m := by
  rw [spectatorStepGap_sub_one]
  have hu := mul_le_mul_of_nonneg_left hupper hr
  nlinarith only [hu, hlower, hbalance, hcost]

theorem eventual_moving_cell_error_budget (k : ℕ) (hk : 2 ≤ k) (ec es : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, ∀ cg : ℝ, cg ≤ (91 / 100 : ℝ) * L →
      2 * cg + 1 + (ec + es) * (2 ^ n : ℕ) ≤
        (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 1 (ec + es))] with L hL n cg hcg
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : ec + es ≤ L := (le_max_right _ _).trans hL
  have hr : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hkR 4
    norm_num at h
    exact h
  have hm := spectatorBulkCount_lower k L
  have hm4 : 4 * L ≤ (spectatorBulkCount k L : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)]
  have he := mul_le_mul_of_nonneg_right hLe (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  have hrl : L ≤ (2 ^ n : ℕ) * L := le_mul_of_one_le_left (by linarith) hr
  have ht := mul_le_mul_of_nonneg_left hm4 (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  nlinarith

/-- The centers may each have an error proportional to `L`.  Since the bulk
size is `k^4 L + O(1)`, the same one-unit gap reserve pays these errors. -/
theorem moving_linear_cell_error_budget (k n : ℕ) (C L cg ec es : ℝ)
    (hC : 0 ≤ C) (hk : 4 * C + 16 ≤ (k : ℝ) ^ 4) (hL : 1 ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L) (he : ec + es ≤ C * L) :
    2 * cg + 1 + (ec + es) * (2 ^ n : ℕ) ≤
      (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ) := by
  have hr : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_lower k L
  have hkL := mul_le_mul_of_nonneg_right hk hL0
  have hCL := mul_nonneg hC hL0
  have hml : (C + 4) * L ≤ (spectatorBulkCount k L : ℝ) := by
    nlinarith only [hm, hkL, hCL, hL]
  have hem := mul_le_mul_of_nonneg_right he (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  have hrL : L ≤ (2 ^ n : ℕ) * L := le_mul_of_one_le_left hL0 hr
  have htotal := mul_le_mul_of_nonneg_left hml
    (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  nlinarith only [hcg, hL, hem, hrL, htotal]

end Ostmann

end OAI
