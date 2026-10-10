import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section
open scoped ENNReal
namespace Invariant233

open MeasureTheory

theorem continuous_regularizedLogIntegral (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun z : ℂ => ∫ w, Real.log (‖w - z‖ ^ 2 + ε) ∂μ) := by
  have hf : Continuous (fun p : ℂ × ℂ => Real.log (‖p.2 - p.1‖ ^ 2 + ε)) := by
    apply Continuous.log (by fun_prop)
    intro p
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
  have h := continuous_parametric_integral_of_continuous
    (μ := μ) (f := fun z w : ℂ => Real.log (‖w - z‖ ^ 2 + ε)) hf hμ
  change Continuous (fun z : ℂ =>
    ∫ w, Real.log (‖w - z‖ ^ 2 + ε) ∂μ.restrict μ.support) at h
  have hr : μ.restrict μ.support = μ :=
    Measure.restrict_eq_self_of_ae_mem (s := μ.support) μ.support_mem_ae
  rw [hr] at h
  exact h

theorem continuous_regularizedPotentialDeterminant (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun z : ℂ => ENNReal.ofReal
      (Real.exp ((∫ w, Real.log (‖w - z‖ ^ 2 + ε) ∂μ) / 2))) := by
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_regularizedLogIntegral μ hμ ε hε).div_const 2))

theorem upperSemicontinuous_logarithmicPotentialDeterminant
    (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support) :
    UpperSemicontinuous (logarithmicPotentialDeterminant μ) := by
  exact upperSemicontinuous_iInf fun ε =>
    (continuous_regularizedPotentialDeterminant μ hμ ε.val ε.property).upperSemicontinuous

theorem continuousAt_logarithmicPotentialDeterminant_of_eq_zero
    (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {z : ℂ} (hz : logarithmicPotentialDeterminant μ z = 0) :
    ContinuousAt (logarithmicPotentialDeterminant μ) z := by
  refine continuousAt_iff_lower_upperSemicontinuousAt.mpr
    ⟨?_, upperSemicontinuous_logarithmicPotentialDeterminant μ hμ z⟩
  intro r hr
  rw [hz] at hr
  exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ r from bot_le) hr).elim

end Invariant233

end

end OAI
