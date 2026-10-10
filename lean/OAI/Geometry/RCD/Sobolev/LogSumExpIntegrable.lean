import OAI.Geometry.RCD.Sobolev.LogSumExpIntegral

namespace OAI

/-! # Integrability of the logarithmic sum from its two logarithms -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem log_sum_exp_abs_le (x y : ℝ) :
    |Real.log (Real.exp x+Real.exp y)| ≤ |x|+|y|+Real.log 2 := by
  have hlow : x ≤ Real.log (Real.exp x+Real.exp y) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x)
      (le_add_of_nonneg_right (Real.exp_pos y).le)
  have hx : Real.exp x ≤ Real.exp (|x|+|y|) :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
  have hy : Real.exp y ≤ Real.exp (|x|+|y|) :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x)))
  have hu := Real.log_le_log (add_pos (Real.exp_pos x) (Real.exp_pos y))
    (show Real.exp x+Real.exp y ≤ 2*Real.exp (|x|+|y|) by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hu
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le x,abs_nonneg y]
  · linarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_log_sum_exp (μ : Measure Ω) [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => Real.log (Real.exp (f x)+Real.exp (g x))) μ := by
  have hm : AEMeasurable (fun x => Real.log (Real.exp (f x)+Real.exp (g x))) μ :=
    (hf.aestronglyMeasurable.aemeasurable.exp.add hg.aestronglyMeasurable.aemeasurable.exp).log
  apply ((hf.abs.add hg.abs).add (integrable_const (Real.log 2))).mono' hm.aestronglyMeasurable
  exact .of_forall fun x => by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using log_sum_exp_abs_le (f x) (g x)

theorem log_sum_exp_integral_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Real.log (Real.exp (∫ x, f x ∂μ)+Real.exp (∫ x, g x ∂μ)) ≤
      ∫ x, Real.log (Real.exp (f x)+Real.exp (g x)) ∂μ :=
  log_sum_exp_integral μ hf hg (integrable_log_sum_exp μ hf hg)

end RegularPointCoordinates

end

end OAI
