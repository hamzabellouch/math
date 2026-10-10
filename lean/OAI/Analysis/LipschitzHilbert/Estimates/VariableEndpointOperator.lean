import OAI.Analysis.LipschitzHilbert.Fourier.VariableEndpointKernel
import OAI.Analysis.LipschitzHilbert.Estimates.ShortL2Operator
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValue

namespace OAI

/-! Uniform L2 control of the error caused by measurable changes of both
time endpoints, with no regularity assumption on the endpoint factor. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def endpointKernelError (epsilon R : ℝ) (a : (ℝ×ℝ) → ℝ)
    (p : ℝ×(ℝ×ℝ)) : ℂ :=
  sharpTimeKernel (epsilon*a p.2) (R*a p.2) p.1-sharpTimeKernel epsilon R p.1

theorem endpointKernelError_measurable (epsilon R : ℝ) (a : (ℝ×ℝ) → ℝ)
    (ha : Measurable a) : Measurable (endpointKernelError epsilon R a) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) =>
      sharpTimeKernel (epsilon*a p.2) (R*a p.2) p.1) := by
    unfold sharpTimeKernel
    have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) |
        epsilon*a p.2 < |p.1| ∧ |p.1| < R*a p.2} :=
      by measurability
    exact (show Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1 : ℂ)⁻¹) by fun_prop).ite hs measurable_const
  exact hm.sub ((sharpTimeKernel_measurable epsilon R).comp measurable_fst)

def endpointErrorOperator (epsilon R : ℝ) (a u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, endpointKernelError epsilon R a (t,z)*shortSample u f t z

theorem endpointErrorOperator_energy (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (a u : (ℝ×ℝ) → ℝ) (ham : Measurable a)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    MemLp (endpointErrorOperator epsilon R a u f) 2 planeMeasure ∧
      (∫ z, ‖endpointErrorOperator epsilon R a u f z‖^2 ∂planeMeasure)≤
        4*(12*Real.pi)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have h := dominatedKernelAverage_energy (endpointKernelError epsilon R a)
    (endpointKernelError_measurable epsilon R a ham) (endpointErrorMajorant epsilon R)
    (endpointErrorMajorant_measurable epsilon R) (endpointErrorMajorant_integrable epsilon R he hR)
    (fun t => endpointErrorMajorant_nonneg epsilon R t he hR)
    (fun p => sharpTimeKernel_scaled_diff epsilon R (a p.2) p.1 he hR (ha p.2) (ha1 p.2))
    (fun p => shortSample u f p.1 p.2) (shortSample_measurable u hu.continuous.measurable f hfm)
    (4*∫ z, ‖f z‖^2 ∂planeMeasure) (fun t => (shortSample_energy u hu f hfm hf t).1)
    (fun t => (shortSample_energy u hu f hfm hf t).2)
  rw [endpointErrorMajorant_integral epsilon R he hR] at h
  exact ⟨h.1,h.2.trans_eq (by ring)⟩

theorem endpointErrorOperator_bound (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (a u : (ℝ×ℝ) → ℝ) (ham : Measurable a)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (endpointErrorOperator epsilon R a u f) 2 planeMeasure≤
      ENNReal.ofReal ((24*Real.pi)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨hm,he2⟩ := endpointErrorOperator_energy epsilon R he hR a u ham ha ha1 hu f
    f.continuous.measurable (f.memLp 2 planeMeasure)
  rw [←memLp_toL2_norm_sq planeMeasure _ hm,
    ←memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)] at he2
  change ‖hm.toLp (endpointErrorOperator epsilon R a u f)‖^2≤
    4*(12*Real.pi)^2*‖f.toLp 2 planeMeasure‖^2 at he2
  have hn : ‖hm.toLp (endpointErrorOperator epsilon R a u f)‖≤
      (24*Real.pi)*‖f.toLp 2 planeMeasure‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    exact he2.trans_eq (by ring)
  rw [←Lp.enorm_toLp hm, ←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem endpointErrorOperator_eq_sub (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (hR : R≤1/4) (a u : (ℝ×ℝ) → ℝ)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    endpointErrorOperator epsilon R a u f z=
      productSymmetricTruncation u (epsilon*a z) (R*a z) f z-
        shortSlopeOperator (sharpTimeKernel epsilon R) u f z := by
  have ha0 : 0<a z := by linarith [ha z]
  have hR0 := he.trans_le heR
  have hj := sharpTimeKernel_integrable (epsilon*a z) (R*a z)
    (mul_pos he ha0) (mul_pos hR0 ha0)
  have hk := sharpTimeKernel_integrable epsilon R he hR0
  have hrep : endpointErrorOperator epsilon R a u f z=
      shortSlopeOperator (fun t => sharpTimeKernel (epsilon*a z) (R*a z) t-
        sharpTimeKernel epsilon R t) u f z := by
    unfold endpointErrorOperator endpointKernelError shortSlopeOperator
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : |t|≤1/4
    · simp only [shortSample,ite_eq_left ht]
    · simp only [shortSample,ite_eq_right ht,mul_zero]
  rw [hrep,shortSlopeOperator_kernel_sub _ _ hj hk]
  congr 1
  exact shortSharp_eq_productSymmetric u f f.continuous _ _ (mul_pos he ha0)
    (mul_le_mul_of_nonneg_right heR ha0.le) (by nlinarith [ha1 z]) z

end LipschitzHilbert.PacketRepresentation

end

end OAI
