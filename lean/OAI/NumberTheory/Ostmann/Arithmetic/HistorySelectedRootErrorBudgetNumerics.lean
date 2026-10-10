import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedResidualBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedRootErrorBudget
open Construction Conclusion Filter HistoryGiantFrequencyCount HistorySelectedResidualBudget

theorem actual_root_card_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ) ≤
      Real.exp (actualFrequencyCost Bs BD Bz k*L) := by
  rw [allowedFrequency_card]
  push_cast
  apply (actual_allowedFrequency_le Bs BD Bz k L hm hl).trans
  apply Real.exp_le_exp.mpr
  let C := scaleLinearConstant Bs BD Bz k+1
  have hC : 0 ≤ C := by dsimp only [C]; linarith [scaleLinearConstant_pos Bs BD Bz k]
  have hpow : (1:ℝ) ≤ (4:ℝ)^k := one_le_pow₀ (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ 4*C*(bulkSize k L:ℝ) by positivity)
  have hsize := mul_le_mul_of_nonneg_left (bulkSize_bounds k hL).2
    (show 0 ≤ 4*(4:ℝ)^k*C by positivity)
  change 2*C*(bulkSize k L:ℝ) ≤ 4*(4:ℝ)^k*C*bulkScale k*L
  nlinarith [show 0 ≤ C*(bulkSize k L:ℝ) by positivity]

theorem root_error_le_residual (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L) (hC : 0 ≤ actualFrequencyCost Bs BD Bz k)
    {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
      Real.exp (-Real.exp ((21/2000:ℝ)*L)) ≤
      residualBudget 1 0 0 0 (actualFrequencyCost Bs BD Bz k) L := by
  have hpoly : L ≤ (L+1)^2 := by nlinarith [sq_nonneg L]
  have he := (actual_root_card_le Bs BD Bz k L hL hm hl).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpoly hC))
  simpa only [residualBudget,one_mul,zero_mul,add_zero] using
    mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-Real.exp ((21/2000:ℝ)*L)))

theorem selected_root_error_eventually (Bs BD Bz H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
      Real.exp (-Real.exp ((21/2000:ℝ)*L)) ≤
      Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) := by
  have hC := (actualFrequencyCost_pos Bs BD Bz hk).le
  filter_upwards [selected_residualBudget_eventually Bs BD Bz 1 0 0 0
    (actualFrequencyCost Bs BD Bz k) H (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hC hH hk, (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L he hm hL
  intro l hl
  exact (root_error_le_residual Bs BD Bz k L hL (by exact_mod_cast hm) hC hl).trans (he l hl)

theorem selected_root_error_bulk_eventually (Bs BD Bz H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
      Real.exp (-Real.exp ((21/2000:ℝ)*L)) ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  have hC := (actualFrequencyCost_pos Bs BD Bz hk).le
  filter_upwards [selected_residualBudget_bulk_eventually 1 0 0 0
    (actualFrequencyCost Bs BD Bz k) H (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hC hH k, (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L he hm hL
  intro l hl
  exact (root_error_le_residual Bs BD Bz k L hL (by exact_mod_cast hm) hC hl).trans he

end Ostmann.Arithmetic.HistorySelectedRootErrorBudget

end

end OAI
