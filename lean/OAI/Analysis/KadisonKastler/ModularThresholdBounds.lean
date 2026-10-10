import OAI.Analysis.KadisonKastler.ModularSpectralCuts

namespace OAI

/-! # Relative widths of the bounded modular spectral coordinates -/

namespace KadisonKastler

theorem modularCutThreshold_relative_width {r δ s : ℝ} (hδ : 0 ≤ δ)
    (hslo : modularCutThreshold (r+δ) ≤ s) (hshi : s ≤ modularCutThreshold r) :
    |s-modularCutThreshold r| ≤ (Real.exp δ-1)*modularCutThreshold r ∧
      |s-modularCutThreshold r| ≤ (Real.exp δ-1)*(1-modularCutThreshold r) := by
  have hE : 1 ≤ Real.exp δ := Real.one_le_exp_iff.mpr hδ
  have hA : 0 < Real.exp r := Real.exp_pos r
  have hAE : 0 < Real.exp r*Real.exp δ := mul_pos hA (Real.exp_pos δ)
  have hden : 0 < 1+Real.exp r*Real.exp δ := by positivity
  have hden' : 0 < 1+Real.exp r := by positivity
  have hbase : 0 ≤ Real.exp δ-1 := sub_nonneg.mpr hE
  have hratio : Real.exp r/(1+Real.exp r*Real.exp δ) ≤ 1 := by
    apply (div_le_one hden).mpr
    have hh := mul_le_mul_of_nonneg_left hE hA.le
    nlinarith
  have hdiff : modularCutThreshold r-modularCutThreshold (r+δ) =
      ((Real.exp δ-1)/(1+Real.exp r)) *
        (Real.exp r/(1+Real.exp r*Real.exp δ)) := by
    unfold modularCutThreshold
    rw [Real.exp_add]
    field_simp
    ring
  have hfirst : modularCutThreshold r - modularCutThreshold (r+δ) ≤
      (Real.exp δ-1)*modularCutThreshold r := by
    rw [hdiff]
    calc
      _ ≤ ((Real.exp δ-1)/(1+Real.exp r))*1 :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg hbase hden'.le)
      _ = _ := by simp only [mul_one, modularCutThreshold, div_eq_mul_inv]
  have hsecond : modularCutThreshold r - modularCutThreshold (r+δ) ≤
      (Real.exp δ-1)*(1-modularCutThreshold r) := by
    have heq : modularCutThreshold r-modularCutThreshold (r+δ) =
        ((Real.exp δ-1)*(1-modularCutThreshold r))/(1+Real.exp r*Real.exp δ) := by
      unfold modularCutThreshold
      rw [Real.exp_add]
      field_simp
      ring
    rw [heq]
    exact div_le_self (mul_nonneg hbase
      (sub_nonneg.mpr (modularCutThreshold_lt_one r).le)) (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hshi)]
  constructor <;> linarith

end KadisonKastler

end OAI
