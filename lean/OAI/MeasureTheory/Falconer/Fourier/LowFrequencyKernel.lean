import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierTests
import OAI.MeasureTheory.Falconer.Graphs.SourceSpatialEnergy

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseSchwartz_integrable (f : 𝓢(ℝ, ℂ)) : Integrable (sourceInverseKernel f) := by
  have h := (𝓕 f).integrable.comp_div (by positivity : 2*Real.pi ≠ 0)
  change Integrable (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑f) (x/(2*Real.pi)))
  convert h.smul ((2*Real.pi)⁻¹) using 1
  funext x
  rw [Pi.smul_apply, SchwartzMap.fourier_coe]

noncomputable def sourceLowpassSchwartz : 𝓢(ℝ, ℂ) :=
  (sourceShellBump.hasCompactSupport.toSchwartzMap sourceShellBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem sourceLowpassSchwartz_apply (r : ℝ) :
    sourceLowpassSchwartz r = (sourceShellLowpass 0 r : ℂ) := by
  simp [sourceLowpassSchwartz, sourceShellLowpass]

noncomputable def sourceLowKernel : ℝ → ℂ := sourceInverseKernel sourceLowpassSchwartz

 theorem sourceLowKernel_integrable : Integrable sourceLowKernel :=
  sourceInverseSchwartz_integrable sourceLowpassSchwartz

noncomputable def sourceLowTerm (τ : FiniteMeasure ℝ) : Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1 sourceLowKernel
    (sourceInverseKernel_continuous _ sourceLowpassSchwartz.integrable)
    sourceLowKernel_integrable τ).1).toLp (kernelMeasureConvolution sourceLowKernel τ)

 theorem schwartz_charFun_integrable (f : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * charFun τ r) := by
  apply (f.integrable.norm.mul_const (τ.real univ)).mono' (by fun_prop)
  filter_upwards with r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_charFun_le r) (norm_nonneg _)

 theorem schwartzKernelMeasureConvolution_test (f : 𝓢(ℝ, ℂ))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * kernelMeasureConvolution (sourceInverseKernel f) τ x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi))) := by
  have he : kernelMeasureConvolution (sourceInverseKernel f) τ =
      sourceInverseKernel (fun r => f r * charFun τ r) :=
    funext (sourceInverseKernel_measure f f.continuous f.integrable τ)
  rw [he, sourceInverseKernel_pairing _ (schwartz_charFun_integrable f τ) φ]
  simp only [mul_assoc]

 theorem schwartz_cutoff_test_integrable (f φ : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi)))) := by
  have h2 := (schwartz_charFun_integrable f τ)
  have hb : ∃ C : ℝ, ∀ r, ‖𝓕 φ (r/(2*Real.pi))‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (𝓕 φ).decay 0 0
    exact ⟨C, fun r => by simpa using hC (r/(2*Real.pi))⟩
  obtain ⟨C,hC⟩ := hb
  apply (h2.norm.mul_const C).mono' (by fun_prop)
  filter_upwards with r
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)

end PlanarFalconer

end OAI
