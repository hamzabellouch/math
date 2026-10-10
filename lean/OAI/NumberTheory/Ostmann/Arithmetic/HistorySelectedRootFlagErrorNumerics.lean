import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootErrorBudgetNumerics

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedRootFlagError
open Construction Conclusion Filter HistoryGiantFrequencyCount
open HistorySelectedRootErrorBudget HistorySelectedResidualBudget

theorem root_flag_error_le_residual (Bs BD Bz F D : ℝ) (k : ℕ) (L : ℝ)
    (hL : 0≤L) (hm : 1≤bulkSize k L) (hF : 0≤F)
    (hC : 0≤actualFrequencyCost Bs BD Bz k) {l : ℕ} (hl : l≤k) :
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
      Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) ≤
      residualBudget 0 F 0 0 (|D|+actualFrequencyCost Bs BD Bz k) L := by
  have hpoly : L≤(L+1)^2 := by nlinarith [sq_nonneg L]
  have hroot := (actual_root_card_le Bs BD Bz k L hL hm hl).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpoly hC))
  have hD : Real.exp (D*(L+1)^2)≤Real.exp (|D| *(L+1)^2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _))
  calc
    _ ≤ Real.exp (actualFrequencyCost Bs BD Bz k*(L+1)^2)*F*
        Real.exp (|D| *(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hroot hF) hD (Real.exp_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) hF)
    _ = residualBudget 0 F 0 0 (|D|+actualFrequencyCost Bs BD Bz k) L := by
      simp only [residualBudget,zero_mul,zero_add,add_zero]
      rw [add_mul,Real.exp_add]
      ring

theorem selected_root_flag_error_eventually (Bs BD Bz F D H : ℝ)
    (hF : 0≤F) (hH : 0≤H) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  have hC := (actualFrequencyCost_pos Bs BD Bz hk).le
  have hD := add_nonneg (abs_nonneg D) hC
  filter_upwards [selected_residualBudget_eventually Bs BD Bz 0 F 0 0
    (|D|+actualFrequencyCost Bs BD Bz k) H (by norm_num) hF (by norm_num) (by norm_num)
    hD hH hk,selected_residualBudget_bulk_eventually 0 F 0 0
    (|D|+actualFrequencyCost Bs BD Bz k) H (by norm_num) hF (by norm_num) (by norm_num)
    hD hH k,(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L hf hb hm hL
  intro l hl
  have he := root_flag_error_le_residual Bs BD Bz F D k L hL (by exact_mod_cast hm) hF hC hl
  exact ⟨he.trans (hf l hl),he.trans hb⟩

theorem selected_root_kernel_flag_error_eventually (Bs BD Bz D H : ℝ)
    (hH : 0≤H) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
        (2:ℝ)^(4*k*2^k)*Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*
        (2:ℝ)^(4*k*2^k)*Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((3/2000:ℝ)*L)) ≤
          Real.exp (-H*(bulkSize k L:ℝ)) :=
  selected_root_flag_error_eventually Bs BD Bz ((2:ℝ)^(4*k*2^k)) D H (by positivity) hH hk

end Ostmann.Arithmetic.HistorySelectedRootFlagError

end

end OAI
