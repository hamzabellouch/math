import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Fourier.SchwartzLpTests
import OAI.MeasureTheory.Falconer.Graphs.SourceSpatialEnergy
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.FalconerCompletion.Fourier.BandTermSubOfLe

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal FourierTransform SchwartzMap
instance complexOfPositive_finite (μ : FiniteMeasure ℝ) : IsFiniteMeasure (complexOfPositive μ).variation := by
  rw [complexOfPositive_variation]
  infer_instance
lemma complexConv_memLp_two (ν : ComplexMeasure ℝ) (n : ℕ) : MemLp (complexConv ν n) 2 volume := by
  rw [complexConv_inverse]
  exact sourceInverseKernel_memLp_two _ (memLp_one_iff_integrable.mp (complexMultiplier_memLp ν n 1))
    (complexMultiplier_memLp ν n 2)
lemma complexConv_energy (ν : ComplexMeasure ℝ) (n : ℕ) :
    (∫ x, ‖complexConv ν n x‖^2) ≤ (2*Real.pi)⁻¹ * complexShellEnergy ν (n+1) := by
  rw [complexConv_inverse,sourceInverseKernel_plancherel _
    (memLp_one_iff_integrable.mp (complexMultiplier_memLp ν n 1)) (complexMultiplier_memLp ν n 2)]
  exact mul_le_mul_of_nonneg_left (complexMultiplier_energy_le ν n) (by positivity)
noncomputable def complexBand1 (ν : ComplexMeasure ℝ) (n : ℕ) : Lp (α:=ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (complexConv_integrable ν n)).toLp (complexConv ν n)
noncomputable def complexBand2 (ν : ComplexMeasure ℝ) (n : ℕ) : Lp (α:=ℝ) ℂ 2 volume :=
  (complexConv_memLp_two ν n).toLp (complexConv ν n)
lemma complexBand1_norm (ν : ComplexMeasure ℝ) [IsFiniteMeasure ν.variation] (n : ℕ) :
    ‖complexBand1 ν n‖ ≤ (2*ν.variation.real univ) * ∫ x, ‖sourceShellKernel 0 x‖ := by
  rw [complexBand1,Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm (complexConv_integrable ν n).aestronglyMeasurable,
    ←integral_norm_eq_lintegral_enorm (complexConv_integrable ν n).aestronglyMeasurable]
  exact complexConv_L1_bound ν n
lemma complexBand2_norm (ν : ComplexMeasure ℝ) (n : ℕ) :
    ‖complexBand2 ν n‖ ≤ Real.sqrt ((2*Real.pi)⁻¹) * Real.sqrt (complexShellEnergy ν (n+1)) := by
  have he : ‖complexBand2 ν n‖^2 ≤ (2*Real.pi)⁻¹ * complexShellEnergy ν (n+1) := by
    rw [complexBand2,←integral_sq_norm_toLp]
    exact complexConv_energy ν n
  have hs := Real.sqrt_le_sqrt he
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_mul (by positivity : 0 ≤ (2*Real.pi)⁻¹)] using hs
lemma complex_band_recombine (μ : FiniteMeasure ℝ) (ν : ComplexMeasure ℝ) [IsFiniteMeasure ν.variation]
    (n : ℕ) (φ : 𝓢(ℝ,ℂ)) :
    schwartzLpTest 1 φ (complexBand1 (complexOfPositive μ-ν) n) +
      schwartzLpTest 2 φ (complexBand2 ν n) = schwartzLpTest 1 φ (bandTerm n (μ : Measure ℝ)) := by
  rw [complexBand1,complexBand2,schwartzLpTest_toLp,schwartzLpTest_toLp,schwartz_bandTerm,
    complexConv_sub,complexConv_positive]
  have ht := (φ.memLp_top volume).integrable_mul
    (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 (μ : Measure ℝ) n).1)
  have hv := (φ.memLp_top volume).integrable_mul
    (memLp_one_iff_integrable.mpr (complexConv_integrable ν n))
  change Integrable (fun x => φ x * kernelMeasureConvolution (sourceShellKernel n) (μ : Measure ℝ) x) at ht
  change Integrable (fun x => φ x * complexConv ν n x) at hv
  simp only [Pi.sub_apply,mul_sub]
  rw [integral_sub ht hv,sub_add_cancel]

end CurrentFalconer.MonotoneShell
end
end

end OAI
