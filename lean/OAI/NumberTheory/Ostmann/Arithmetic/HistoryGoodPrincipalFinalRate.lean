import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGoodPrincipalFinalRate
open Conclusion Filter

def finalRateConstant (Bs BD Bz : ℝ) (k : ℕ) (A : ℝ) : ℝ :=
  scaleLinearConstant Bs BD Bz k+A*(2:ℝ)^k

theorem finalRateConstant_pos (Bs BD Bz : ℝ) (k : ℕ) {A : ℝ} (hA : 0≤A) :
    0<finalRateConstant Bs BD Bz k A := by
  have hc := scaleLinearConstant_pos Bs BD Bz k
  have ha : 0≤A*(2:ℝ)^k := mul_nonneg hA (by positivity)
  unfold finalRateConstant
  linarith

theorem frequencyBudget_final_rate_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {A : ℝ} (hA : 0≤A) (hm : 1≤bulkSize k L) {l : ℕ} (hl : l≤k) :
    frequencyBudget Bs BD Bz k L l+A*(2:ℝ)^k*(bulkSize k L:ℝ) ≤
      finalRateConstant Bs BD Bz k A*(2:ℝ)^l*(bulkSize k L:ℝ) := by
  have hf := frequencyBudget_le_linear Bs BD Bz k L hm hl
  have hp : (1:ℝ)≤(2:ℝ)^l := one_le_pow₀ (by norm_num)
  have hH := (finalRateConstant_pos Bs BD Bz k hA).le
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hH) (Nat.cast_nonneg (bulkSize k L): (0:ℝ)≤bulkSize k L)
  calc
    _ ≤ scaleLinearConstant Bs BD Bz k*(bulkSize k L:ℝ)+
      A*(2:ℝ)^k*(bulkSize k L:ℝ) := add_le_add hf le_rfl
    _ = finalRateConstant Bs BD Bz k A*(bulkSize k L:ℝ) := by
      unfold finalRateConstant
      ring
    _ ≤ _ := by simpa only [mul_one] using hmul

theorem exp_final_rate_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {A : ℝ} (hA : 0≤A) (hm : 1≤bulkSize k L) {l : ℕ} (hl : l≤k) :
    Real.exp (-finalRateConstant Bs BD Bz k A*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
      Real.exp (-(frequencyBudget Bs BD Bz k L l+
        A*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using neg_le_neg (frequencyBudget_final_rate_le Bs BD Bz k L hA hm hl)

theorem eventually_frequencyBudget_final_rate (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k)
    {A : ℝ} (hA : 0≤A) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ L : ℝ in atTop, ∀ l : ℕ, l≤k →
      frequencyBudget Bs BD Bz k L l+A*(2:ℝ)^k*(bulkSize k L:ℝ) ≤
        H*(2:ℝ)^l*(bulkSize k L:ℝ) ∧
      Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
        Real.exp (-(frequencyBudget Bs BD Bz k L l+
          A*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
  refine ⟨finalRateConstant Bs BD Bz k A,finalRateConstant_pos Bs BD Bz k hA,?_⟩
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  have hm' : 1≤bulkSize k L := by exact_mod_cast hm
  intro l hl
  exact ⟨frequencyBudget_final_rate_le Bs BD Bz k L hA hm' hl,
    exp_final_rate_le Bs BD Bz k L hA hm' hl⟩

theorem eventually_frequencyBudget_covariance_rate (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ L : ℝ in atTop, ∀ l : ℕ, l≤k →
      frequencyBudget Bs BD Bz k L l+65*(2:ℝ)^k*(bulkSize k L:ℝ) ≤
        H*(2:ℝ)^l*(bulkSize k L:ℝ) ∧
      Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
        Real.exp (-(frequencyBudget Bs BD Bz k L l+
          65*(2:ℝ)^k*(bulkSize k L:ℝ))) :=
  eventually_frequencyBudget_final_rate Bs BD Bz hk (by norm_num : (0:ℝ)≤65)

end Ostmann.Arithmetic.HistoryGoodPrincipalFinalRate

end

end OAI
