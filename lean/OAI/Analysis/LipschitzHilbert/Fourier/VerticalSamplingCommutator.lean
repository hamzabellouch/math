import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingDifference

namespace OAI

/-! The bin/sampling commutator is the integral of the actual sampling-order difference. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def sampledFunction (u : (ℝ×ℝ) → ℝ) (t : ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-t*u z)

def verticalSamplingCommutator (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (t : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  verticalConvolution K (sampledFunction u t f) z-
    sampledFunction u t (verticalConvolution K f) z

theorem verticalSamplingCommutator_eq (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (t : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) :
    verticalSamplingCommutator K u t f z=
      ∫ s, K s*verticalSamplingDifference f u t s z := by
  have hi1 : Integrable (fun s => K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s))) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact (hK.aestronglyMeasurable.mul (f.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [] with s
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  have hi2 : Integrable (fun s => K s*f (z.1-t,z.2-t*u z-s)) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact (hK.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [] with s
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  change (∫ s, K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s)))-
    (∫ s, K s*f (z.1-t,z.2-t*u z-s))=_
  rw [←integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [] with s
  change K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s))-
    K s*f (z.1-t,z.2-t*u z-s)=
    K s*(f (z.1-t,z.2-s-t*u (z.1,z.2-s))-f (z.1-t,z.2-s-t*u z))
  rw [show z.2-t*u z-s=z.2-s-t*u z by ring,mul_sub]

end LipschitzHilbert.PacketRepresentation

end

end OAI
