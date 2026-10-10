import OAI.MeasureTheory.Falconer.Fourier.SchwartzLpTests
import OAI.MeasureTheory.Falconer.Measures.MonotoneMeasureMass

namespace OAI

/-!
# Low-pass terms for the decreasing-measure shell argument

The Schwartz Fourier cutoffs represent the low-pass terms of shell
reconstruction. The L¹ bound is uniform in the dyadic cutoff index.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem sourceShellLowpass_compact (n : ℕ) : HasCompactSupport (sourceShellLowpass n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((2 : ℝ)^(n+1)))
  intro r hr
  apply sourceShellLowpass_zero
  have hn : ¬ |r| ≤ (2 : ℝ)^(n+1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hr
  exact le_of_lt (lt_of_not_ge hn)

noncomputable def dyadicLowpassSchwartz (n : ℕ) : 𝓢(ℝ, ℂ) :=
  ((sourceShellLowpass_compact n).toSchwartzMap (sourceShellLowpass_smooth n)).postcompCLM
    Complex.ofRealCLM

@[simp] theorem dyadicLowpassSchwartz_apply (n : ℕ) (r : ℝ) :
    dyadicLowpassSchwartz n r = (sourceShellLowpass n r : ℂ) := rfl

noncomputable def dyadicLowKernel (n : ℕ) : ℝ → ℂ :=
  sourceInverseKernel (dyadicLowpassSchwartz n)

theorem dyadicLowKernel_dilate (n : ℕ) (x : ℝ) :
    dyadicLowKernel n x = (2 : ℝ)^n • sourceLowKernel ((2 : ℝ)^n * x) := by
  have he : (dyadicLowpassSchwartz n : ℝ → ℂ) =
      fun r => sourceLowpassSchwartz (r / (2 : ℝ)^n) := by
    funext r
    simp only [dyadicLowpassSchwartz_apply, sourceLowpassSchwartz_apply,
      sourceShellLowpass, pow_zero, div_one]
  rw [dyadicLowKernel, he, sourceInverseKernel_dilate _ (by positivity),
    abs_of_pos (by positivity : (0 : ℝ) < 2^n)]
  rfl

theorem dyadicLowKernel_integrable (n : ℕ) : Integrable (dyadicLowKernel n) :=
  sourceInverseSchwartz_integrable _

theorem dyadicLowKernel_continuous (n : ℕ) : Continuous (dyadicLowKernel n) :=
  sourceInverseKernel_continuous _ (dyadicLowpassSchwartz n).integrable

theorem dyadicLowKernel_uniform_L1 (n : ℕ) :
    (∫ x, ‖dyadicLowKernel n x‖) = ∫ x, ‖sourceLowKernel x‖ := by
  simp_rw [dyadicLowKernel_dilate n, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2^n)]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x => ‖sourceLowKernel x‖) ((2 : ℝ)^n), smul_eq_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2^n)⁻¹)]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

noncomputable def dyadicLowTerm (n : ℕ) (τ : FiniteMeasure ℝ) :
    Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1 (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).1).toLp
      (kernelMeasureConvolution (dyadicLowKernel n) τ)

theorem dyadicLowTerm_norm_le (n : ℕ) (τ : FiniteMeasure ℝ) :
    ‖dyadicLowTerm n τ‖ ≤ (τ : Measure ℝ).real univ * ∫ x, ‖sourceLowKernel x‖ := by
  have hi := (kernelMeasureConvolution_L1 (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).1
  rw [dyadicLowTerm, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  simpa only [dyadicLowKernel_uniform_L1] using
    (kernelMeasureConvolution_L1 (dyadicLowKernel n)
      (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).2

theorem dyadicLowTerm_test (n : ℕ) (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (dyadicLowTerm n τ) =
      (2 * Real.pi)⁻¹ • ∫ r, sourceShellLowpass n r •
        (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi))) := by
  rw [dyadicLowTerm, schwartzLpTest_toLp]
  simpa only [dyadicLowKernel, dyadicLowpassSchwartz_apply, Complex.real_smul] using
    schwartzKernelMeasureConvolution_test (dyadicLowpassSchwartz n) τ φ

/-- Uniform low-pass bounds make the variation series absolutely convergent.
The increments here are the actual positive differences of finite measures. -/
theorem summable_dyadicLowTerm_decrements (α : ℕ → FiniteMeasure ℝ)
    (hα : Antitone (fun n => (α n : Measure ℝ))) :
    Summable (fun n => ‖dyadicLowTerm (n + 1)
      ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩ -
      dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖) := by
  let C := ∫ x, ‖sourceLowKernel x‖
  have hs := (Falconer.summable_antitone_measure_decrements
    (fun n => (α n : Measure ℝ)) hα).mul_left (2 * C)
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  calc
    _ ≤ ‖dyadicLowTerm (n + 1)
        ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖ +
        ‖dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖ := norm_sub_le _ _
    _ ≤ ((α n : Measure ℝ) - α (n + 1)).real univ * C +
        ((α n : Measure ℝ) - α (n + 1)).real univ * C :=
      add_le_add (dyadicLowTerm_norm_le _ _) (dyadicLowTerm_norm_le _ _)
    _ = _ := by ring

end PlanarFalconer
namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- Convolution preserves sums of finite positive measures in L¹. -/
theorem dyadicLowTerm_add (n : ℕ) (μ ν : FiniteMeasure ℝ) :
    dyadicLowTerm n (μ + ν) = dyadicLowTerm n μ + dyadicLowTerm n ν := by
  apply Lp.ext
  have hsum := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) (μ + ν)).1).coeFn_toLp
  have hμ := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) μ).1).coeFn_toLp
  have hν := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) ν).1).coeFn_toLp
  have hiμ := (kernelMeasureConvolution_prod_integrable (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) μ).prod_right_ae
  have hiν := (kernelMeasureConvolution_prod_integrable (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) ν).prod_right_ae
  filter_upwards [hsum, hμ, hν, Lp.coeFn_add (dyadicLowTerm n μ) (dyadicLowTerm n ν),
    hiμ, hiν] with x hxsum hxμ hxν hxadd hxintμ hxintν
  rw [hxadd]
  simp only [Pi.add_apply]
  change _ = _ at hxsum hxμ hxν
  rw [show dyadicLowTerm n (μ + ν) x = kernelMeasureConvolution (dyadicLowKernel n)
    (μ + ν) x from hxsum, show dyadicLowTerm n μ x =
    kernelMeasureConvolution (dyadicLowKernel n) μ x from hxμ,
    show dyadicLowTerm n ν x = kernelMeasureConvolution (dyadicLowKernel n) ν x from hxν]
  exact integral_add_measure hxintμ hxintν

/-- The positive measure difference is sent to the difference of low-pass terms. -/
theorem dyadicLowTerm_sub_of_le (n : ℕ) (μ ν : FiniteMeasure ℝ)
    (h : (ν : Measure ℝ) ≤ μ) :
    dyadicLowTerm n ⟨(μ : Measure ℝ) - ν, inferInstance⟩ =
      dyadicLowTerm n μ - dyadicLowTerm n ν := by
  let ξ : FiniteMeasure ℝ := ⟨(μ : Measure ℝ) - ν, inferInstance⟩
  change dyadicLowTerm n ξ = dyadicLowTerm n μ - dyadicLowTerm n ν
  apply eq_sub_iff_add_eq.mpr
  rw [← dyadicLowTerm_add]
  congr 1
  apply Subtype.ext
  exact Measure.sub_add_cancel_of_le h

/-- Finite summation by parts in the actual L¹ space of low-pass convolutions.
The final term is a single low-pass difference applied to the remaining tail. -/
theorem dyadicLowTerm_summation_by_parts (α : ℕ → FiniteMeasure ℝ)
    (hα : Antitone (fun n => (α n : Measure ℝ))) (M : ℕ) :
    (∑ j ∈ Finset.range M, (dyadicLowTerm (j + 1) (α j) - dyadicLowTerm j (α j))) =
      (∑ n ∈ Finset.range M,
        (dyadicLowTerm (n + 1) ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩ -
        dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩)) +
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      dyadicLowTerm_sub_of_le _ _ _ (hα (Nat.le_succ M)),
      dyadicLowTerm_sub_of_le _ _ _ (hα (Nat.le_succ M))]
    abel

end PlanarFalconer
namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- The dyadic cutoffs converge to the original measure in Schwartz tests. -/
theorem dyadicLowTerm_test_tendsto (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun n => schwartzLpTest 1 φ (dyadicLowTerm n τ)) atTop
      (𝓝 (∫ x, φ x ∂(τ : Measure ℝ))) := by
  simp_rw [dyadicLowTerm_test]
  have h := (sourceShellLowpass_fourier_test (τ : Measure ℝ)
    (fun r => 𝓕 φ (r / (2 * Real.pi)))
    ((𝓕 φ).integrable.comp_div (by positivity))).const_smul ((2 * Real.pi)⁻¹)
  rw [source_characteristic_schwartz_test] at h
  exact h

/-- The difference of adjacent cutoff tests is exactly the existing shell
kernel test, with no change to the Fourier convention. -/
theorem dyadicLowTerm_band_test (n : ℕ) (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (dyadicLowTerm (n + 1) τ - dyadicLowTerm n τ) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [map_sub, dyadicLowTerm_test, dyadicLowTerm_test]
  have hi (m : ℕ) : Integrable (fun r => sourceShellLowpass m r •
      (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi)))) := by
    simpa only [dyadicLowpassSchwartz_apply, Complex.real_smul] using
      schwartz_cutoff_test_integrable (dyadicLowpassSchwartz m) φ τ
  rw [← smul_sub, ← integral_sub (hi _) (hi _)]
  simp_rw [← sub_smul]
  change (2 * Real.pi)⁻¹ • (∫ r, sourceShellBand n r •
    (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi)))) = _
  simpa only [sourceShellKernel, sourceShellSchwartz_apply, Complex.real_smul] using
    (schwartzKernelMeasureConvolution_test (sourceShellSchwartz n) τ φ).symm

/-- A decreasing family's remaining tail vanishes after any varying cutoff,
provided only that its mass tends to zero. -/
theorem dyadicLowTerm_tail_tendsto (α : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hle : ∀ n, (τ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ) atTop (𝓝 0))
    (k : ℕ → ℕ) :
    Tendsto (fun n => dyadicLowTerm (k n) (α n) - dyadicLowTerm (k n) τ)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ *
      ∫ x, ‖sourceLowKernel x‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hmass.mul_const (∫ x, ‖sourceLowKernel x‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) ht
  rw [← dyadicLowTerm_sub_of_le _ _ _ (hle n)]
  exact dyadicLowTerm_norm_le _ _

end PlanarFalconer

end OAI
