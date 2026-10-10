import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

noncomputable def kernelMeasureConvolution (K : ℝ → ℂ) (τ : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ y, K (x-y) ∂τ

theorem kernelMeasureConvolution_prod_integrable (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun z : ℝ × ℝ => K (z.1-z.2)) (volume.prod τ) := by
  apply (integrable_prod_iff' (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with y
    exact hi.comp_sub_right y
  · have he : (fun y : ℝ => ∫ x : ℝ, ‖K (x-y)‖) = fun _ => ∫ x, ‖K x‖ := by
      funext y
      exact integral_sub_right_eq_self (fun x => ‖K x‖) y
    change Integrable (fun y : ℝ => ∫ x : ℝ, ‖K (x-y)‖) τ
    rw [he]
    exact integrable_const _

theorem kernelMeasureConvolution_L1 (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (kernelMeasureConvolution K τ) ∧
      (∫ x, ‖kernelMeasureConvolution K τ x‖) ≤ τ.real univ * ∫ x, ‖K x‖ := by
  have hp := kernelMeasureConvolution_prod_integrable K hK hi τ
  have hc : Integrable (kernelMeasureConvolution K τ) := hp.integral_prod_left
  refine ⟨hc, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, ‖K (x-y)‖ ∂τ := integral_mono hc.norm hp.integral_norm_prod_left
      (fun x => norm_integral_le_integral_norm _)
    _ = ∫ y, ∫ x, ‖K (x-y)‖ ∂volume ∂τ := integral_integral_swap hp.norm
    _ = _ := by
      simp_rw [integral_sub_right_eq_self (fun x => ‖K x‖)]
      rw [integral_const, smul_eq_mul]

theorem sourceShellKernel_continuous (n : ℕ) : Continuous (sourceShellKernel n) := by
  have h := (𝓕 (sourceShellSchwartz n)).continuous.comp
    (continuous_id.div_const (2*Real.pi))
  change Continuous (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑(sourceShellSchwartz n)) (x/(2*Real.pi)))
  convert (continuous_const (y := (2*Real.pi)⁻¹)).smul h using 1
  funext x
  simp only [id_eq, SchwartzMap.fourier_coe]
  rfl

theorem shellKernelMeasureConvolution_L1 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Integrable (kernelMeasureConvolution (sourceShellKernel n) τ) ∧
      (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖) ≤
        τ.real univ * ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ

end PlanarFalconer

end OAI
