import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.LowFrequencyKernel
import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.FalconerCompletion.Measures.MeasureRealSub
import OAI.MeasureTheory.FalconerCompletion.Shells.ComplexShellEnergyEq

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal
noncomputable def bandTerm (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] : Lp (α:=ℝ) ℂ 1 volume :=
  lowTerm (n+1) μ - lowTerm n μ
lemma bandTerm_representative (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (bandTerm n μ : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (sourceShellKernel n) μ := by
  have h1 := (kernelMeasureConvolution_prod_integrable (lowKernel (n+1))
    (lowKernel_continuous _) (lowKernel_integrable _) μ).prod_right_ae
  have h0 := (kernelMeasureConvolution_prod_integrable (lowKernel n)
    (lowKernel_continuous _) (lowKernel_integrable _) μ).prod_right_ae
  filter_upwards [Lp.coeFn_sub (lowTerm (n+1) μ) (lowTerm n μ),
    (by exact MemLp.coeFn_toLp _ : (lowTerm (n+1) μ : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (lowKernel (n+1)) μ),
    (by exact MemLp.coeFn_toLp _ : (lowTerm n μ : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (lowKernel n) μ),h1,h0]
    with x hsub hprev hcur hi1 hi0
  change (lowTerm (n+1) μ-lowTerm n μ) x = _
  rw [hsub,Pi.sub_apply,hprev,hcur,sourceShellKernel_eq_sub_low]
  exact (integral_sub hi1 hi0).symm
where
  sourceShellKernel_eq_sub_low := shellKernel_eq_sub_low n
lemma variation_summation_by_parts (J N : ℕ) (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (hmono : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (αinf : Measure ℝ) ≤ (α n : Measure ℝ)) :
    (∑ n ∈ Finset.range N, bandTerm (n+J) ((α (n+1) : Measure ℝ)-(αinf : Measure ℝ))) =
      lowTerm (N+J) ((α N : Measure ℝ)-(αinf : Measure ℝ)) -
      lowTerm J ((α 0 : Measure ℝ)-(αinf : Measure ℝ)) +
      ∑ n ∈ Finset.range N, lowTerm (n+J) ((α n : Measure ℝ)-(α (n+1) : Measure ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    simp only [bandTerm,lowTerm_sub_of_le _ _ _ (hle _),
      lowTerm_sub_of_le _ _ _ (hmono (Nat.le_succ _))]
    have hn : N+J+1 = N+1+J := by omega
    rw [hn]
    abel
lemma monotone_correction_converges (J : ℕ) (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (hmono : Antitone (fun n => (α n : Measure ℝ)))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s))) :
    ∃ Z : Lp (α:=ℝ) ℂ 1 volume,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        bandTerm (n+J) ((α (n+1) : Measure ℝ)-(αinf : Measure ℝ))) atTop (𝓝 Z) := by
  let d (n : ℕ) := lowTerm (n+J) ((α n : Measure ℝ)-(α (n+1) : Measure ℝ))
  have hd : Summable (fun n => ‖d n‖) := by
    apply ((monotone_drop_mass_summable α hmono).mul_right (∫ x, ‖sourceLowKernel x‖)).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => lowTerm_norm_le _ _)
  have ht : Tendsto (fun N => lowTerm (N+J) ((α N : Measure ℝ)-(αinf : Measure ℝ))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => lowTerm_norm_le _ _)
    simpa using (monotone_tail_mass_tendsto_zero α αinf hmono hlim).mul_const (∫ x, ‖sourceLowKernel x‖)
  refine ⟨-lowTerm J ((α 0 : Measure ℝ)-(αinf : Measure ℝ)) + ∑' n, d n,?_⟩
  simp_rw [variation_summation_by_parts J _ α αinf hmono (monotone_limit_le α αinf hmono hlim)]
  simpa only [zero_sub] using (ht.sub_const (lowTerm J ((α 0 : Measure ℝ)-(αinf : Measure ℝ)))).add
    hd.of_norm.hasSum.tendsto_sum_nat

end CurrentFalconer.MonotoneShell
end
end

end OAI
