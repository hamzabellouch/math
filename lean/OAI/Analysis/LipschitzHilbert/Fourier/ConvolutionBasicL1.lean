import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionPairing

namespace OAI

/-! Integrability and a uniform pointwise bound for convolution of an
integrable kernel with a Schwartz function. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_integrable (K f : ℝ → ℂ) (hK : Integrable K) (hf : Integrable f) :
    Integrable (lineConvolution K f) := by
  have hj : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  exact hj.integral_prod_left

theorem lineConvolution_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have hh := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
  rw [integral_mul_const] at hh
  exact hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
