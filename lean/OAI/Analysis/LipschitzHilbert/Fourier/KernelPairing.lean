import OAI.Analysis.LipschitzHilbert.Fourier.KernelDifferencePairing

namespace OAI

/-! Measurability and kernel linearity of the actual scalar pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def kernelPairing (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) : ℂ :=
  ∫ z, slopeKernelOperator K u f z*star (g z) ∂planeMeasure

theorem slopeKernelOperator_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (slopeKernelOperator K u f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      K p.2*f (p.1.1-p.2,p.1.2-p.2*u p.1)) := by fun_prop
  have hi : Measurable (fun z : ℝ×ℝ => ∫ t : ℝ, K t*f (z.1-t,z.2-t*u z)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact hi

theorem slopeKernelOperator_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    ‖slopeKernelOperator K u f z‖≤
      (∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f := by
  have h := norm_integral_le_of_norm_le
    (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f))
    (Filter.Eventually.of_forall fun t => show
      ‖K t*f (z.1-t,z.2-t*u z)‖≤‖K t‖*SchwartzMap.seminorm ℝ 0 0 f from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _))
  simpa only [slopeKernelOperator,integral_mul_const] using h

theorem kernelPairing_integrable (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (fun z => slopeKernelOperator K u f z*star (g z)) planeMeasure := by
  have hm := slopeKernelOperator_measurable K hKm u hu f
  apply ((g.integrable (μ:=planeMeasure)).norm.const_mul
    ((∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f)).mono'
  · exact (show Measurable (fun z => slopeKernelOperator K u f z*star (g z)) from by fun_prop).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_right (slopeKernelOperator_uniform K hK u f z) (norm_nonneg _)

theorem kernelPairing_add (K J : ℝ → ℂ) (hKm : Measurable K) (hJm : Measurable J)
    (hK : Integrable K) (hJ : Integrable J) (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing (fun t => K t+J t) u f g=kernelPairing K u f g+kernelPairing J u f g := by
  have heq (z : ℝ×ℝ) : slopeKernelOperator (fun t => K t+J t) u f z=
      slopeKernelOperator K u f z+slopeKernelOperator J u f z := by
    simp only [slopeKernelOperator,add_mul]
    exact integral_add (slope_integrand_integrable K hK u f z)
      (slope_integrand_integrable J hJ u f z)
  simp only [kernelPairing,heq,add_mul]
  exact integral_add (kernelPairing_integrable K hKm hK u hu f g)
    (kernelPairing_integrable J hJm hJ u hu f g)

theorem kernelPairing_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) :
    kernelPairing K u (c • f) g=c*kernelPairing K u f g := by
  have heq (z : ℝ×ℝ) : slopeKernelOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=
      c*slopeKernelOperator K u f z := by
    unfold slopeKernelOperator
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [smul_apply,smul_eq_mul]
    ring
  simp only [kernelPairing,heq,mul_assoc]
  exact integral_const_mul _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
