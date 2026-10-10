import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionKernel

namespace OAI

/-! Bounded line convolutions have finite local square energy. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have h := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [lineConvolution,integral_mul_const] using h

theorem lineConvolution_integrableOn_sq (K : SchwartzMap ℝ ℂ) (f : ℝ → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B)
    (S : Set ℝ) (hS : volume S≠⊤) :
    IntegrableOn (fun x => ‖lineConvolution K f x‖^2) S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have hh : MemLp (lineConvolution K f) 2 (volume.restrict S) :=
    MemLp.of_bound (lineConvolution_measurable K K.continuous.measurable f hfm).aestronglyMeasurable.restrict
      ((∫ t, ‖K t‖)*B) (Filter.Eventually.of_forall (lineConvolution_bound K f K.integrable B hf))
  exact hh.integrable_norm_pow (by decide : 2≠0)

end LipschitzHilbert.PacketRepresentation

end

end OAI
