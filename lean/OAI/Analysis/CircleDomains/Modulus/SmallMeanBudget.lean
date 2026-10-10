import OAI.Analysis.CircleDomains.Modulus.SourceStokesBudgetEstimate

namespace OAI

/-! The small occupation and punctured hit norms used by compact arc
reduction imply the quantitative strict Stokes budget needed for exclusion. -/

open Set MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 def meanBudgetConstant (B : ℝ≥0) (R : ℝ) : ℝ :=
  2 * Real.sqrt Real.pi * R * (1 + 2 * (B : ℝ)) + 2 * Real.pi * R

 def meanBudgetTolerance (B : ℝ≥0) (R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (δ / (meanBudgetConstant B R + 1))

 theorem meanBudgetTolerance_pos (B : ℝ≥0) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    0 < meanBudgetTolerance B R δ := by
  apply ENNReal.ofReal_pos.mpr
  apply div_pos hδ
  have hc : 0 ≤ meanBudgetConstant B R := by unfold meanBudgetConstant; positivity
  linarith

 theorem meanBudgetTolerance_ne_top (B : ℝ≥0) (R δ : ℝ) :
    meanBudgetTolerance B R δ ≠ ∞ := ENNReal.ofReal_ne_top

 theorem mean_budget_lt_of_small_norms
    (B : ℝ≥0) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {a b : ℝ≥0∞} (hsmall : a + b < meanBudgetTolerance B R δ) :
    2 * Real.sqrt Real.pi * R *
        (meanBudgetTolerance B R δ + (2 * (B : ℝ≥0∞)) * a).toReal +
      2 * Real.pi * R * b.toReal < δ := by
  let t : ℝ := δ / (meanBudgetConstant B R + 1)
  have hc : 0 ≤ meanBudgetConstant B R := by unfold meanBudgetConstant; positivity
  have ht : 0 < t := div_pos hδ (by linarith)
  have ha : a ≤ ENNReal.ofReal t := (le_add_right le_rfl).trans hsmall.le
  have hb : b ≤ ENNReal.ofReal t := (le_add_left le_rfl).trans hsmall.le
  have ha' : a.toReal ≤ t := by
    simpa only [ENNReal.toReal_ofReal ht.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ha
  have hb' : b.toReal ≤ t := by
    simpa only [ENNReal.toReal_ofReal ht.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have he : (meanBudgetTolerance B R δ + (2 * (B : ℝ≥0∞)) * a).toReal =
      t + (2 * (B : ℝ)) * a.toReal := by
    rw [ENNReal.toReal_add (meanBudgetTolerance_ne_top B R δ)
      (ENNReal.mul_ne_top (by finiteness) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha)),
      ENNReal.toReal_mul]
    simp only [meanBudgetTolerance, ENNReal.toReal_ofReal ht.le, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_mul, t]
  rw [he]
  calc
    _ ≤ 2 * Real.sqrt Real.pi * R * (t + (2 * (B : ℝ)) * t) +
        2 * Real.pi * R * t := by gcongr
    _ = meanBudgetConstant B R * t := by unfold meanBudgetConstant; ring
    _ < (meanBudgetConstant B R + 1) * t := by nlinarith
    _ = δ := mul_div_cancel₀ δ (by linarith : meanBudgetConstant B R + 1 ≠ 0)

end CircleDomainRigidity

end

end OAI
