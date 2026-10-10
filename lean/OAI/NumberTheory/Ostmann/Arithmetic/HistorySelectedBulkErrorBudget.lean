import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedBulkErrorBudgetBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedBulkErrorBudget
open Construction Conclusion Filter HistorySelectedResidualBudget

theorem selected_paid_bulk_error_eventually (Bs BD Bz H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
    let error := ((Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
      Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)))*
      (192*Real.exp (-Real.exp (ScaleBudget.bulk.target*L)))
    error ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
    error ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  have hD := bulkErrorCost_nonneg Bs BD Bz k
  filter_upwards [selected_residualBudget_eventually Bs BD Bz 0 0 192 0
      (bulkErrorCost Bs BD Bz k) H (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hD hH hk,
    selected_residualBudget_bulk_eventually 0 0 192 0 (bulkErrorCost Bs BD Bz k)
      H (by norm_num) (by norm_num) (by norm_num) (by norm_num) hD hH k,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L hfreq hbulk hm hL
  intro l hl
  have he := paid_bulk_error_le_residual Bs BD Bz k L hL (by exact_mod_cast hm) hl
  exact ⟨he.trans (hfreq l hl),he.trans hbulk⟩

end Ostmann.Arithmetic.HistorySelectedBulkErrorBudget

end

end OAI
