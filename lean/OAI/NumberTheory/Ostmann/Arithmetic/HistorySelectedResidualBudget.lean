import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedResidualBudgetBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedResidualBudget
open Conclusion Filter

theorem selected_residualBudget_eventually (Bs BD Bz G F B C D H : ℝ)
    (hG : 0 ≤ G) (hF : 0 ≤ F) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hH : 0 ≤ H) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
      residualBudget G F B C D L ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) := by
  let R := (scaleLinearConstant Bs BD Bz k+H)*bulkScale k
  have hS := (scaleLinearConstant_pos Bs BD Bz k).le
  have hR : 0 ≤ R := by dsimp [R,bulkScale]; positivity
  filter_upwards [residualBudget_eventually G F B C D R hG hF hB hC hD hR,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L he hm hL
  intro l hl
  have hfreq := frequencyBudget_le_linear Bs BD Bz k L (by exact_mod_cast hm) hl
  have hbulk := mul_le_mul_of_nonneg_left (bulkSize_bounds k hL).2
    (add_nonneg hS hH)
  apply he.trans
  apply Real.exp_le_exp.mpr
  dsimp only [R]
  nlinarith

theorem selected_residualBudget_bulk_eventually (G F B C D H : ℝ)
    (hG : 0 ≤ G) (hF : 0 ≤ F) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hH : 0 ≤ H) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, residualBudget G F B C D L ≤
      Real.exp (-H*(bulkSize k L:ℝ)) := by
  have hR : 0 ≤ H*bulkScale k := by unfold bulkScale; positivity
  filter_upwards [residualBudget_eventually G F B C D (H*bulkScale k)
    hG hF hB hC hD hR,eventually_ge_atTop (0:ℝ)] with L he hL
  apply he.trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (bulkSize_bounds k hL).2 hH
  nlinarith

end Ostmann.Arithmetic.HistorySelectedResidualBudget

end

end OAI
