import OAI.Analysis.LipschitzHilbert.Fourier.KernelPairing
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! Positive compact mollifiers preserve the unit bound and give actual
Schwartz approximants for compactly supported measurable tests. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution Pointwise
namespace LipschitzHilbert.PacketRepresentation

def compactMollification (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  ((phi.hasCompactSupport_normed (μ:=planeMeasure)).convolution (L:=ContinuousLinearMap.lsmul ℝ ℝ)
    hc).toSchwartzMap
      ((phi.hasCompactSupport_normed (μ:=planeMeasure)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed hf.locallyIntegrable)

theorem compactMollification_apply (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) (z : ℝ×ℝ) :
    compactMollification phi f hf hc z=
      ∫ t, phi.normed planeMeasure t • f (z-t) ∂planeMeasure := rfl

theorem compactMollification_unit (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) : ∀ z, ‖compactMollification phi f hf hc z‖≤1 := by
  intro z
  rw [compactMollification_apply]
  have h := norm_integral_le_of_norm_le (phi.integrable_normed (μ:=planeMeasure))
    (Filter.Eventually.of_forall fun t => show
      ‖phi.normed planeMeasure t • f (z-t)‖≤phi.normed planeMeasure t from by
      rw [norm_smul,Real.norm_of_nonneg (phi.nonneg_normed _)]
      exact mul_le_of_le_one_right (phi.nonneg_normed _) (hb _))
  simpa only [phi.integral_normed] using h

theorem compactMollification_support (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    support (compactMollification phi f hf hc)⊆
      Metric.ball 0 phi.rOut+support f := by
  change support (phi.normed planeMeasure ⋆[ContinuousLinearMap.lsmul ℝ ℝ,planeMeasure] f)⊆_
  rw [←phi.support_normed_eq (μ:=planeMeasure)]
  exact support_convolution_subset _

end LipschitzHilbert.PacketRepresentation

end

end OAI
