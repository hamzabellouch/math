import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.LowFrequencyKernel
import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Fourier.SchwartzLpTests
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.Falconer.Shells.ShellTestConvergence
import OAI.MeasureTheory.FalconerCompletion.Estimates.BandTerm

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal FourierTransform SchwartzMap
lemma bandTerm_sub_of_le (n : ℕ) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν ≤ μ) : bandTerm n (μ-ν) = bandTerm n μ-bandTerm n ν := by
  simp only [bandTerm,lowTerm_sub_of_le _ _ _ h]
  abel
lemma bandTerm_telescope (J N : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    lowTerm (N+J) μ = lowTerm J μ + ∑ n ∈ Finset.range N, bandTerm (n+J) μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,←add_assoc,←ih]
    simp only [bandTerm]
    have hn : N+J+1 = N+1+J := by omega
    rw [hn]
    abel
lemma schwartz_bandTerm (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : 𝓢(ℝ,ℂ)) :
    schwartzLpTest 1 φ (bandTerm n μ) = ∫ x, φ x*kernelMeasureConvolution (sourceShellKernel n) μ x := by
  rw [schwartzLpTest_apply]
  apply integral_congr_ae
  filter_upwards [bandTerm_representative n μ] with x hx
  rw [hx]
lemma lowTerm_test_tendsto (J : ℕ) (μ : FiniteMeasure ℝ) (φ : 𝓢(ℝ,ℂ)) :
    Tendsto (fun N => schwartzLpTest 1 φ (lowTerm (N+J) (μ : Measure ℝ))) atTop
      (𝓝 (∫ x, φ x ∂(μ : Measure ℝ))) := by
  have he (N : ℕ) : schwartzLpTest 1 φ (lowTerm N (μ : Measure ℝ)) =
      schwartzLpTest 1 φ (sourceLowTerm μ) +
        ∑ n ∈ Finset.range N, ∫ x, φ x*kernelMeasureConvolution (sourceShellKernel n) (μ : Measure ℝ) x := by
    rw [show N = N+0 from (Nat.add_zero _).symm,bandTerm_telescope 0 N,lowTerm_zero,map_add,map_sum]
    simp only [Nat.add_zero,schwartz_bandTerm]
    congr 2
  have h := sourceShell_spatial_test_tendsto μ φ
  simp_rw [←he] at h
  exact h.comp (tendsto_add_atTop_nat J)

end CurrentFalconer.MonotoneShell
end
end

end OAI
