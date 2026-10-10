import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.LowFrequencyKernel
import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Graphs.SourceSpatialEnergy
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.Falconer.Shells.Shells
import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseAdd

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal
lemma complexShellEnergy_eq (ν : ComplexMeasure ℝ) (N : ℕ) : complexShellEnergy ν N =
    ∫ r in dyadicShell N, ‖complexChar ν r‖^2 := by
  have hs := (dyadicShell_compact N).measurableSet
  have he : (dyadicShell N).indicator (fun r => ‖complexChar ν r‖^2) =
      fun r => (dyadicShell N).indicator (fun r => ‖complexFourier ν r‖^2) (-r) := by
    funext r
    have hr : -r ∈ dyadicShell N ↔ r ∈ dyadicShell N := by simp [dyadicShell]
    by_cases hm : r ∈ dyadicShell N
    · simp [hm,hr.mpr hm,complexChar_eq_fourier]
    · simp [hm,show -r ∉ dyadicShell N from fun h => hm (hr.mp h)]
  rw [complexShellEnergy,←integral_indicator hs,←integral_indicator hs,he,integral_neg_eq_self]
lemma complexShellEnergy_nonneg (ν : ComplexMeasure ℝ) (N : ℕ) : 0 ≤ complexShellEnergy ν N :=
  integral_nonneg (fun _ => sq_nonneg _)
lemma complexMultiplier_energy_le (ν : ComplexMeasure ℝ) (n : ℕ) :
    (∫ r, ‖complexMultiplier ν n r‖^2) ≤ complexShellEnergy ν (n+1) := by
  have he : (∫ r in dyadicShell (n+1), ‖complexMultiplier ν n r‖^2) =
      ∫ r, ‖complexMultiplier ν n r‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
      rw [complexMultiplier_zero ν n r hr,norm_zero,zero_pow (by norm_num)])
  rw [←he,complexShellEnergy_eq]
  apply setIntegral_mono_on
    (((complexMultiplier_continuous ν n).norm.pow 2).continuousOn.integrableOn_compact
      (dyadicShell_compact (n+1)))
    (((complexChar_continuous ν).norm.pow 2).continuousOn.integrableOn_compact
      (dyadicShell_compact (n+1))) (dyadicShell_compact (n+1)).measurableSet
  intro r hr
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [complexMultiplier,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (sourceShellBand_abs_le n r) (norm_nonneg _)).trans_eq (one_mul _)

end CurrentFalconer.MonotoneShell
end
end

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal FourierTransform SchwartzMap
noncomputable def lowKernel (n : ℕ) (x : ℝ) : ℂ :=
  (2:ℝ)^n • sourceLowKernel ((2:ℝ)^n*x)
lemma lowKernel_continuous (n : ℕ) : Continuous (lowKernel n) := by
  unfold lowKernel sourceLowKernel
  exact (continuous_const (y := (2:ℝ)^n)).smul ((sourceInverseKernel_continuous _ sourceLowpassSchwartz.integrable).comp
    ((continuous_const (y := (2:ℝ)^n)).mul continuous_id))
lemma lowKernel_integrable (n : ℕ) : Integrable (lowKernel n) := by
  have hi := sourceLowKernel_integrable.comp_div (by positivity : ((2:ℝ)^n)⁻¹ ≠ 0)
  have he : (fun x => sourceLowKernel (x/((2:ℝ)^n)⁻¹)) =
      fun x => sourceLowKernel ((2:ℝ)^n*x) := by funext x;simp [div_eq_mul_inv,mul_comm]
  rw [he] at hi
  exact hi.smul ((2:ℝ)^n)
lemma lowKernel_uniform (n : ℕ) :
    (∫ x, ‖lowKernel n x‖) = ∫ x, ‖sourceLowKernel x‖ := by
  simp_rw [lowKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖sourceLowKernel x‖) ((2:ℝ)^n),
    smul_eq_mul,abs_of_pos (by positivity : (0:ℝ)<((2:ℝ)^n)⁻¹)]
  rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
lemma lowKernel_inverse (n : ℕ) : lowKernel n =
    sourceInverseKernel (fun r => (sourceShellLowpass n r : ℂ)) := by
  funext x
  have h : (fun r => (sourceShellLowpass n r : ℂ)) =
      fun r => sourceLowpassSchwartz (r/(2:ℝ)^n) := by
    funext r
    simp [sourceShellLowpass]
  rw [h,sourceInverseKernel_dilate _ (by positivity),abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rfl
lemma shellKernel_eq_sub_low (n : ℕ) : sourceShellKernel n = lowKernel (n+1)-lowKernel n := by
  rw [lowKernel_inverse,lowKernel_inverse]
  have hi (m : ℕ) : Integrable (fun r => (sourceShellLowpass m r : ℂ)) := by
    convert sourceLowpassSchwartz.integrable.comp_div (by positivity : (2:ℝ)^m ≠ 0) using 1
    funext r
    simp [sourceShellLowpass]
  have he : (sourceShellSchwartz n : ℝ → ℂ) =
      (fun r => (sourceShellLowpass (n+1) r : ℂ)) - (fun r => (sourceShellLowpass n r : ℂ)) := by
    funext r
    simp [sourceShellBand]
  funext x
  rw [sourceShellKernel,he,sourceInverseKernel]
  change (2*Real.pi)⁻¹ • (∫ r, Real.fourierChar (-inner ℝ r (x/(2*Real.pi))) •
      ((sourceShellLowpass (n+1) r : ℂ)-(sourceShellLowpass n r : ℂ))) = _
  simp only [smul_sub]
  have hj (m : ℕ) : Integrable (fun r => Real.fourierChar (-inner ℝ r (x/(2*Real.pi))) •
      (sourceShellLowpass m r : ℂ)) := by
    exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (x/(2*Real.pi))).2 (hi m)
  rw [integral_sub (hj (n+1)) (hj n),smul_sub]
  rfl
noncomputable def lowTerm (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] : Lp (α:=ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1 (lowKernel n)
    (lowKernel_continuous n) (lowKernel_integrable n) μ).1).toLp
      (kernelMeasureConvolution (lowKernel n) μ)
lemma lowTerm_norm_le (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖lowTerm n μ‖ ≤ μ.real univ * (∫ x, ‖sourceLowKernel x‖) := by
  have hconvolution := kernelMeasureConvolution_L1 (lowKernel n)
    (lowKernel_continuous n) (lowKernel_integrable n) μ
  rw [lowTerm,Lp.norm_toLp,eLpNorm_one_eq_lintegral_enorm hconvolution.1.aestronglyMeasurable,
    ←integral_norm_eq_lintegral_enorm hconvolution.1.aestronglyMeasurable]
  simpa only [lowKernel_uniform] using hconvolution.2
lemma lowTerm_add (n : ℕ) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    lowTerm n (μ+ν) = lowTerm n μ + lowTerm n ν := by
  apply Lp.ext
  have hμ := (kernelMeasureConvolution_prod_integrable (lowKernel n)
    (lowKernel_continuous n) (lowKernel_integrable n) μ).prod_right_ae
  have hν := (kernelMeasureConvolution_prod_integrable (lowKernel n)
    (lowKernel_continuous n) (lowKernel_integrable n) ν).prod_right_ae
  filter_upwards [hμ,hν,(by exact MemLp.coeFn_toLp _ :
      (lowTerm n (μ+ν) : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (lowKernel n) (μ+ν)),
    (by exact MemLp.coeFn_toLp _ : (lowTerm n μ : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (lowKernel n) μ),
    (by exact MemLp.coeFn_toLp _ : (lowTerm n ν : ℝ → ℂ) =ᵐ[volume] kernelMeasureConvolution (lowKernel n) ν),
    Lp.coeFn_add (lowTerm n μ) (lowTerm n ν)] with x hxμ hxν hxsum hxμv hxνv hxadd
  rw [hxadd,hxsum,Pi.add_apply,hxμv,hxνv]
  exact integral_add_measure hxμ hxν
lemma lowTerm_sub_of_le (n : ℕ) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν ≤ μ) : lowTerm n (μ-ν) = lowTerm n μ-lowTerm n ν := by
  have he := lowTerm_add n (μ-ν) ν
  simp only [Measure.sub_add_cancel_of_le h] at he
  exact eq_sub_iff_add_eq.mpr he.symm
lemma lowTerm_zero (μ : Measure ℝ) [IsFiniteMeasure μ] : lowTerm 0 μ = sourceLowTerm ⟨μ,inferInstance⟩ := by
  have hk : lowKernel 0 = sourceLowKernel := by funext x;simp [lowKernel]
  unfold lowTerm sourceLowTerm
  congr 1
  rw [hk]
  rfl
end CurrentFalconer.MonotoneShell
end
end

end OAI
