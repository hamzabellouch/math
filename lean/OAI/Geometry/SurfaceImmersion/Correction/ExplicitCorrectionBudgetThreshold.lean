import OAI.Geometry.SurfaceImmersion.Geometry.ExplicitPowerThreshold

namespace OAI

/-! An explicit scale preserving the input and metric correction budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

def correctionBudgetThreshold (A B a N L : ℝ) : ℝ :=
  min (powerThreshold 5 |N*(1+B)| (B-A))
    (powerThreshold 5 |L*(1+2*B)| (a/8))

theorem correctionBudgetThreshold_spec {A B a N L : ℝ} (hAB : A < B) (ha : 0 < a) :
    0 < correctionBudgetThreshold A B a N L ∧
    correctionBudgetThreshold A B a N L ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < correctionBudgetThreshold A B a N L →
      A+N*t^(1/5 : ℝ)*(1+B) ≤ B ∧ L*(1+2*B)*t^(1/5 : ℝ) ≤ a/8 := by
  have h₁ := powerThreshold_spec (n := 5) (by decide) (abs_nonneg (N*(1+B)))
    (sub_pos.mpr hAB) (show ((5 : ℕ) : ℝ)⁻¹ ≤ (1/5 : ℝ) by norm_num)
  have h₂ := powerThreshold_spec (n := 5) (by decide) (abs_nonneg (L*(1+2*B)))
    (show 0 < a/8 by positivity) (show ((5 : ℕ) : ℝ)⁻¹ ≤ (1/5 : ℝ) by norm_num)
  refine ⟨lt_min h₁.1 h₂.1, (min_le_left _ _).trans h₁.2.1,?_⟩
  intro t ht hsmall
  have h₁t := (h₁.2.2 t ht (hsmall.trans_le (min_le_left _ _))).le
  have h₂t := (h₂.2.2 t ht (hsmall.trans_le (min_le_right _ _))).le
  have hpow : 0 ≤ t^(1/5 : ℝ) := Real.rpow_nonneg ht.le _
  have hn := mul_le_mul_of_nonneg_right (le_abs_self (N*(1+B))) hpow
  have hl := mul_le_mul_of_nonneg_right (le_abs_self (L*(1+2*B))) hpow
  constructor
  · nlinarith
  · exact hl.trans h₂t

end ClosedSurfaceR4.ExactCorrection

end

end OAI
