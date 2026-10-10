import OAI.Analysis.LipschitzHilbert.Fourier.ShortKernelPairing
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeCommutation

namespace OAI

/-! A kernel L1 error controls the actual localized bilinear form by the
smaller of the input and test masses. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slope_integrand_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Integrable (fun t => K t*f (z.1-t,z.2-t*u z)) := by
  apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
  · exact hK.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)

theorem slopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (fun t => K t-J t) u f z=
      slopeKernelOperator K u f z-slopeKernelOperator J u f z := by
  simp only [slopeKernelOperator,sub_mul]
  exact integral_sub (slope_integrand_integrable K hK u f z)
    (slope_integrand_integrable J hJ u f z)

theorem shortSlopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator (fun t => K t-J t) u f z=
      shortSlopeOperator K u f z-shortSlopeOperator J u f z := by
  simp only [shortSlopeOperator_eq_kernel]
  have heq : shortTimeKernel (fun t => K t-J t)=
      fun t => shortTimeKernel K t-shortTimeKernel J t := by
    funext t
    unfold shortTimeKernel
    split_ifs <;> simp
  rw [heq]
  exact slopeOperator_kernel_sub _ _ (shortTimeKernel_integrable K hK)
    (shortTimeKernel_integrable J hJ) u f z

theorem kernelDifference_pairing (K J : ℝ → ℂ) (hKm : Measurable K) (hJm : Measurable J)
    (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖(∫ z, slopeKernelOperator K u f z*star (g z) ∂planeMeasure)-
      (∫ z, slopeKernelOperator J u f z*star (g z) ∂planeMeasure)‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*
        (∫ t, ‖K t-J t‖) := by
  have hkp := shortKernel_pairing K hKm hK u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hjp := shortKernel_pairing J hJm hJ u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hdiff := shortKernel_pairing (fun t => K t-J t) (hKm.sub hJm) (hK.sub hJ) u hu
    f g f.continuous.measurable g.continuous.measurable f.integrable g.integrable hf1 hg1
  have heqK (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq K u f g l r hwidth hfstrip hgstrip z
  have heqJ (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq J u f g l r hwidth hfstrip hgstrip z
  simp_rw [←heqK,←heqJ]
  rw [←integral_sub hkp.1 hjp.1]
  have heq (z : ℝ×ℝ) : shortSlopeOperator K u f z*star (g z)-
      shortSlopeOperator J u f z*star (g z)=
        shortSlopeOperator (fun t => K t-J t) u f z*star (g z) := by
    rw [shortSlopeOperator_kernel_sub K J hK hJ]
    ring
  simpa only [heq] using hdiff.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
