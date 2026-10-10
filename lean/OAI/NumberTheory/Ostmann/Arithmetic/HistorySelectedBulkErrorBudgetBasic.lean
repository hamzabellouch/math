import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantRootFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedResidualBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedBulkErrorBudget
open Construction Conclusion Filter HistoryGiantFrequencyCount HistorySelectedResidualBudget

def bulkErrorCost (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  2*actualFrequencyCost Bs BD Bz k+2*(2:ℝ)^k*bulkScale k

theorem bulkErrorCost_nonneg (Bs BD Bz : ℝ) (k : ℕ) :
    0 ≤ bulkErrorCost Bs BD Bz k := by
  have := scaleLinearConstant_pos Bs BD Bz k
  unfold bulkErrorCost actualFrequencyCost bulkScale
  positivity

theorem frequency_compensation_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
      Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤ Real.exp (bulkErrorCost Bs BD Bz k*L) := by
  have hroot := actual_root_pair_card_le Bs BD Bz k L hL hm hl
  have hr : (2:ℝ)^l ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hbulk : 2*(2:ℝ)^l*(bulkSize k L:ℝ) ≤ 2*(2:ℝ)^k*bulkScale k*L := by
    have hsize := mul_le_mul_of_nonneg_left (bulkSize_bounds k hL).2
      (show 0 ≤ 2*(2:ℝ)^l by positivity)
    have hpower := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ 2*bulkScale k*L by unfold bulkScale; positivity)
    nlinarith
  calc
    _ ≤ Real.exp (2*actualFrequencyCost Bs BD Bz k*L)*
      Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) :=
        mul_le_mul_of_nonneg_right hroot (Real.exp_nonneg _)
    _ = Real.exp (2*actualFrequencyCost Bs BD Bz k*L+2*(2:ℝ)^l*(bulkSize k L:ℝ)) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold bulkErrorCost
      nlinarith

theorem paid_bulk_error_le_residual (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    ((Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*
      Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)))*
      (192*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))) ≤
        residualBudget 0 0 192 0 (bulkErrorCost Bs BD Bz k) L := by
  have hpoly : L ≤ (L+1)^2 := by nlinarith [sq_nonneg L]
  have h := (frequency_compensation_le Bs BD Bz k L hL hm hl).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpoly (bulkErrorCost_nonneg Bs BD Bz k)))
  simpa only [residualBudget,zero_mul,zero_add,add_zero] using
    mul_le_mul_of_nonneg_right h
      (show 0 ≤ 192*Real.exp (-Real.exp (ScaleBudget.bulk.target*L)) by positivity)

end Ostmann.Arithmetic.HistorySelectedBulkErrorBudget

end

end OAI
