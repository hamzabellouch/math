import OAI.Analysis.CircleDomains.Sobolev.ModelLocalEnergy
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy

namespace OAI

/-! The two real coordinate differentials of a holomorphic map have the
same pointwise squared norm as its complex derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_real_fderiv_norm_sq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖fderiv ℝ (fun w => (f w).re) z‖^2 = ‖deriv f z‖^2 := by
  have h := (Complex.reCLM.hasFDerivAt.comp z
    (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv
  change ‖fderiv ℝ (Complex.reCLM ∘ f) z‖^2 = _
  rw [h, complexCovector_norm_sq, Complex.sq_norm, Complex.normSq_apply]
  change (1 * deriv f z).re^2+(Complex.I * deriv f z).re^2 = _
  simp only [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, zero_sub, neg_sq]
  ring


 theorem holomorphic_imag_fderiv_norm_sq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖fderiv ℝ (fun w => (f w).im) z‖^2 = ‖deriv f z‖^2 := by
  have h := (Complex.imCLM.hasFDerivAt.comp z
    (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv
  change ‖fderiv ℝ (Complex.imCLM ∘ f) z‖^2 = _
  rw [h, complexCovector_norm_sq, Complex.sq_norm, Complex.normSq_apply]
  change (1 * deriv f z).im^2+(Complex.I * deriv f z).im^2 = _
  simp only [one_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, zero_add]
  ring


 theorem holomorphic_coordinate_memLp {D U : Set ℂ} (hD : IsOpen D)
    (hU : MeasurableSet U) (hUD : U ⊆ D) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hE : Integrable (fun z => ‖deriv f z‖^2) (volume.restrict U)) :
    MemLp (fderiv ℝ (fun z => (f z).re)) 2 (volume.restrict U) ∧
      MemLp (fderiv ℝ (fun z => (f z).im)) 2 (volume.restrict U) := by
  have hcf : ContDiffOn ℝ ∞ f D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hr : ContDiffOn ℝ ∞ (fun z => (f z).re) D :=
    Complex.reCLM.contDiff.comp_contDiffOn hcf
  have hi : ContDiffOn ℝ ∞ (fun z => (f z).im) D :=
    Complex.imCLM.contDiff.comp_contDiffOn hcf
  have hrm := (hr.continuousOn_fderiv_of_isOpen hD (by simp)).mono hUD
  have him := (hi.continuousOn_fderiv_of_isOpen hD (by simp)).mono hUD
  constructor
  · apply (memLp_norm_iff (hrm.aestronglyMeasurable hU)).mp
    apply (memLp_two_iff_integrable_sq (hrm.norm.aestronglyMeasurable hU)).mpr
    apply hE.congr
    filter_upwards [ae_restrict_mem hU] with z hz
    exact (holomorphic_real_fderiv_norm_sq ((hf z (hUD hz)).differentiableAt (hD.mem_nhds (hUD hz)))).symm
  · apply (memLp_norm_iff (him.aestronglyMeasurable hU)).mp
    apply (memLp_two_iff_integrable_sq (him.norm.aestronglyMeasurable hU)).mpr
    apply hE.congr
    filter_upwards [ae_restrict_mem hU] with z hz
    exact (holomorphic_imag_fderiv_norm_sq ((hf z (hUD hz)).differentiableAt (hD.mem_nhds (hUD hz)))).symm

end CircleDomainRigidity

end

end OAI
