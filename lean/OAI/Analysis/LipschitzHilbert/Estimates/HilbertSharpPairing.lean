import OAI.Analysis.LipschitzHilbert.Estimates.HilbertTimeProfile
import OAI.Analysis.LipschitzHilbert.Fourier.KernelDifferencePairing

namespace OAI

/-! Uniform comparison of the actual sharp Hilbert pairing with its finite
annular decomposition, with a restricted mass gain at both endpoints. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSharp_pairing_error :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ l r : ℝ, r-l≤1/4 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
    ‖(∫ z, slopeKernelOperator (sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength))
        u f z*star (g z) ∂planeMeasure)-
      (∫ z, slopeKernelOperator (finiteTimeKernel hilbertTimeKernel N topLength)
        u f z*star (g z) ∂planeMeasure)‖≤
      B*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_sharp_integral
  refine ⟨B,hB,?_⟩
  intro N topLength htop u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  let K := sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength)
  let J := finiteTimeKernel hilbertTimeKernel N topLength
  have hdiff := hkernel N topLength htop
  have hJ : Integrable J := finiteTimeKernel_integrable hilbertTimeKernel N topLength htop
  have hK : Integrable K := by
    have h := hdiff.1.add hJ
    apply h.congr
    filter_upwards [] with t
    change (K t-J t)+J t=K t
    ring
  have h := kernelDifference_pairing K J (sharpTimeKernel_measurable _ _)
    (finiteTimeKernel_measurable hilbertTimeKernel N topLength) hK hJ
    u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  refine h.trans ?_
  calc
    _ ≤ min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*B :=
      mul_le_mul_of_nonneg_left hdiff.2
        (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))
    _ = _ := mul_comm _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
