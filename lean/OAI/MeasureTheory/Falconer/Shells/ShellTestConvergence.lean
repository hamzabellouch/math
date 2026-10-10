import OAI.MeasureTheory.Falconer.Fourier.SchwartzLpTests

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceShell_spatial_test_tendsto (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun N => schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x)
      atTop (𝓝 (∫ x, φ x ∂(τ : Measure ℝ))) := by
  let t : ℝ → ℂ := fun r => charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))
  have hi0 : Integrable (fun r => sourceShellLowpass 0 r • t r) := by
    simpa only [sourceLowpassSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable sourceLowpassSchwartz φ τ
  have hin (n : ℕ) : Integrable (fun r => sourceShellBand n r • t r) := by
    simpa only [sourceShellSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable (sourceShellSchwartz n) φ τ
  have he (N : ℕ) : schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x =
      (2*Real.pi)⁻¹ • ∫ r, (sourceShellLowpass 0 r +
        ∑ n ∈ Finset.range N, sourceShellBand n r) • t r := by
    rw [schwartzLpTest_low]
    simp_rw [sourceShellKernel, schwartzKernelMeasureConvolution_test,
      sourceShellSchwartz_apply, ← Complex.real_smul]
    rw [← Finset.smul_sum, ← smul_add]
    congr 1
    simp_rw [add_smul, Finset.sum_smul]
    rw [integral_add hi0 (integrable_finsetSum _ (fun n _ => hin n)),
      integral_finsetSum _ (fun n _ => hin n)]
  simp_rw [he]
  have h := (sourceShellPartition_fourier_test (τ : Measure ℝ)
    (fun r => 𝓕 φ (r/(2*Real.pi))) ((𝓕 φ).integrable.comp_div (by positivity))).const_smul
    ((2*Real.pi)⁻¹)
  rw [source_characteristic_schwartz_test] at h
  exact h

end PlanarFalconer

end OAI
