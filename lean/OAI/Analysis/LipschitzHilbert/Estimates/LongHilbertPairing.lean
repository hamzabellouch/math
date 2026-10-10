import OAI.Analysis.LipschitzHilbert.Fourier.KernelPairing
import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelL1
import OAI.Analysis.LipschitzHilbert.Fourier.ActualCutoffBandHigh

namespace OAI

/-! The long-time remainder has logarithmic size times the smaller
restricted mass, also for the original vertical projection. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_long_pairing (a R : ℝ) (ha : 0<a) (haR : a≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖kernelPairing (sharpTimeKernel a R) u f g‖≤
      (2*Real.log (R/a))*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have h := (shortKernel_pairing (sharpTimeKernel a R) (sharpTimeKernel_measurable a R)
    (sharpTimeKernel_integrable a R ha (ha.trans_le haR)) u hu f g
    f.continuous.measurable g.continuous.measurable f.integrable g.integrable hf hg).2
  simp_rw [shortSlopeOperator_pairing_eq _ u f g l r hwidth hfstrip hgstrip] at h
  rw [sharpTimeKernel_l1 a R ha haR] at h
  exact h.trans_eq (mul_comm _ _)

theorem sharpHilbertProjection_long_pairing (a R : ℝ) (ha : 0<a) (haR : a≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖kernelPairing (sharpTimeKernel a R) u (schwartzVerticalProjection p w 0 f) g‖≤
      (verticalProjectionCost p*(2*Real.log (R/a)))*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have h := sharpHilbert_long_pairing a R ha haR u hu (normalizedBandProjection p w f) g
    (normalizedBandProjection_uniform p w hw f hf) hg l r hwidth
    (normalizedBandProjection_support p w hw f _ hfstrip) hgstrip
  have hs := (normalizedBandProjection_sizes p w hw f).1
  have hlog : 0≤2*Real.log (R/a) := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg ((one_le_div ha).2 haR)
  unfold kernelPairing
  rw [bandProjection_pairing_normalize]
  calc
    _ ≤ verticalProjectionCost p*((2*Real.log (R/a))*
        min (4*∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left h (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost p*((2*Real.log (R/a))*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      exact mul_le_mul_of_nonneg_left (min_le_min (mul_le_mul_of_nonneg_left hs (by norm_num)) le_rfl) hlog
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
