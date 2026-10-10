import OAI.MeasureTheory.Falconer.Shells.ShellErrorSummability
import OAI.MeasureTheory.Falconer.Fourier.LowFrequencyKernel

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

noncomputable def schwartzLpTest (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ)) :
    Lp (α := ℝ) ℂ p volume →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)

 theorem schwartzLpTest_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : Lp (α := ℝ) ℂ p volume) : schwartzLpTest p φ f = ∫ x, φ x * f x := by
  exact Lp.toTemperedDistribution_apply f φ

 theorem schwartzLpTest_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℝ → ℂ) (hf : MemLp f p volume) :
    schwartzLpTest p φ (hf.toLp f) = ∫ x, φ x * f x := by
  rw [schwartzLpTest_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

 theorem schwartzLpTest_sum_tendsto (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℕ → Lp (α := ℝ) ℂ p volume) (hf : Summable f) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, schwartzLpTest p φ (f n)) atTop
      (𝓝 (schwartzLpTest p φ (∑' n, f n))) := by
  simpa only [Function.comp_def, map_sum] using
    ((schwartzLpTest p φ).continuous.tendsto (∑' n, f n)).comp hf.tendsto_sum_tsum_nat

 theorem schwartzLpTest_shell_recombine (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    schwartzLpTest 1 φ (shellL1Error τ τN n) + schwartzLpTest 2 φ (shellL2Term τN n) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [shellL1Error, shellL2Term, schwartzLpTest_toLp, schwartzLpTest_toLp]
  have ht : Integrable (fun x => φ x * kernelMeasureConvolution (sourceShellKernel n) τ x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 τ n).1)
  have hn : Integrable (fun x => φ x *
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 (τN (n+1)) n).1)
  simp_rw [mul_sub]
  rw [integral_sub ht hn, sub_add_cancel]

 theorem schwartzLpTest_low (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (sourceLowTerm τ) =
      (2*Real.pi)⁻¹ • ∫ r, sourceShellLowpass 0 r •
        (charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))) := by
  rw [sourceLowTerm, schwartzLpTest_toLp]
  simpa only [sourceLowKernel, sourceLowpassSchwartz_apply, Complex.real_smul] using
    schwartzKernelMeasureConvolution_test sourceLowpassSchwartz τ φ

end PlanarFalconer

end OAI
