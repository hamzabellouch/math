import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSmoothCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Smooth cutoffs with a fixed derivative bound after rescaling the collar. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralTransition_fderiv_zero (x : ℝ) (hx : x ∉ Icc (0 : ℝ) 1) :
    fderiv ℝ Real.smoothTransition x=0 := by
  rcases not_and_or.mp hx with hx | hx
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge hx)] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa using h.fderiv_eq (𝕜 := ℝ)
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hx)] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa using h.fderiv_eq (𝕜 := ℝ)

theorem spectralTransition_fderiv_compact :
    HasCompactSupport (fderiv ℝ Real.smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc spectralTransition_fderiv_zero

theorem spectralTransition_temperate : Real.smoothTransition.HasTemperateGrowth := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply Function.HasTemperateGrowth.of_fderiv
    (spectralTransition_fderiv_compact.hasTemperateGrowth
      (hs.fderiv_right (by simp)))
    (hs.differentiable (by simp)) (k := 0) (C := 1)
  intro x
  simpa only [pow_zero,mul_one,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg x)]
    using Real.smoothTransition.le_one x

theorem spectralTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ C := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (fun x => ‖fderiv ℝ Real.smoothTransition x‖) :=
    (hs.fderiv_right (m := ∞) (by simp)).continuous.norm
  obtain ⟨x,hx⟩ := hc.exists_forall_ge_of_hasCompactSupport
    spectralTransition_fderiv_compact.norm
  refine ⟨‖fderiv ℝ Real.smoothTransition x‖,norm_nonneg _,fun y => ?_⟩
  calc
    ‖deriv Real.smoothTransition y‖ = ‖fderiv ℝ Real.smoothTransition y 1‖ := by
      rw [fderiv_eq_smul_deriv,one_smul]
    _ ≤ ‖fderiv ℝ Real.smoothTransition y‖ := by
      simpa using (fderiv ℝ Real.smoothTransition y).le_opNorm (1 : ℝ)
    _ ≤ _ := hx y

noncomputable def spectralCollarCutoff (l ε r : ℝ) : ℝ :=
  Real.smoothTransition ((r-l-ε)/ε)

noncomputable def spectralCollarCutoffDerivative (l ε r : ℝ) : ℝ :=
  deriv Real.smoothTransition ((r-l-ε)/ε)/ε

theorem spectralCollarCutoff_hasDerivAt (l ε r : ℝ) :
    HasDerivAt (spectralCollarCutoff l ε) (spectralCollarCutoffDerivative l ε r) r := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h := (hs.differentiable (by simp) _).hasDerivAt.comp r
    (((hasDerivAt_id r).sub_const l).sub_const ε |>.div_const ε)
  change HasDerivAt (fun x => Real.smoothTransition ((x-l-ε)/ε))
    (deriv Real.smoothTransition ((r-l-ε)/ε)/ε) r
  simpa only [Function.comp_def,id_eq,div_eq_mul_inv,one_mul] using h

theorem spectralCollarCutoff_temperate (l ε : ℝ) :
    (spectralCollarCutoff l ε).HasTemperateGrowth := by
  have ha : (fun r : ℝ => (r-l-ε)*ε⁻¹).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.id.sub (.const l)).sub (.const ε)).mul (.const ε⁻¹)
  change (fun r => Real.smoothTransition ((r-l-ε)/ε)).HasTemperateGrowth
  simpa only [Function.comp_def,div_eq_mul_inv] using
    spectralTransition_temperate.comp ha

theorem spectralCollarCutoff_zero (l ε r : ℝ) (hε : 0 < ε) (hr : r ≤ l+ε) :
    spectralCollarCutoff l ε r=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

theorem spectralCollarCutoff_one (l ε r : ℝ) (hε : 0 < ε) (hr : l+2*ε ≤ r) :
    spectralCollarCutoff l ε r=1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by linarith)

theorem spectralCollarCutoff_bounds (l ε r : ℝ) :
    0 ≤ spectralCollarCutoff l ε r ∧ spectralCollarCutoff l ε r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem spectralCollarCutoffDerivative_bound (C : ℝ)
    (hC : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ C) (l ε r : ℝ) (hε : 0 < ε) :
    ‖spectralCollarCutoffDerivative l ε r‖ ≤ C/ε := by
  simpa only [spectralCollarCutoffDerivative,norm_div,Real.norm_eq_abs,abs_of_pos hε]
    using div_le_div_of_nonneg_right (hC ((r-l-ε)/ε)) hε.le

end DefocusingNLS

end OAI
