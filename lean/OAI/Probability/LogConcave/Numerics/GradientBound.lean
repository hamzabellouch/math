import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GradientIntegral
open MeasureTheory Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gradient_bound {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∃C : ℝ,0≤C ∧ ∀y,‖fderiv ℝ φ y‖≤C := by
  obtain ⟨C,hC⟩ := (hφc.fderiv ℝ).exists_bound_of_continuousOn
    (hφ.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C 0,le_max_right _ _,fun y => ?_⟩
  by_cases hy : y∈tsupport (fderiv ℝ φ)
  · exact (hC y hy).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy,norm_zero]
    exact le_max_right _ _

lemma continuous_gradient_expectation {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X) (u : E) :
    Continuous (fun t => ∫y,fderiv ℝ φ y (X (t,y) u) ∂μ) := by
  have hc : Continuous (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (hX.clm_apply continuous_const)
  have he (t : ℝ) : (∫y in tsupport φ,fderiv ℝ φ y (X (t,y) u) ∂μ)=
      ∫y,fderiv ℝ φ y (X (t,y) u) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [(HasFDerivAt.of_notMem_tsupport ℝ hy).fderiv]
    rfl
  simpa only [he] using
    (continuous_parametric_integral_of_continuous (μ:=μ) (f:=fun t y => fderiv ℝ φ y (X (t,y) u)) hc hφc)

lemma gradient_time_space_integrable {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X)
    {T C : ℝ} (hC : 0≤C) (hbound : ∀t∈Icc (0:ℝ) T,∀y,‖X (t,y)‖≤C) (u : E) :
    Integrable (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) ((volume.restrict (Icc 0 T)).prod μ) := by
  obtain ⟨D,_,hDb⟩ := gradient_bound hφ hφc
  have hc : Continuous (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (hX.clm_apply continuous_const)
  apply (integrable_const (D*C*‖u‖)).mono' hc.aestronglyMeasurable
  have ha : ∀ᵐ p ∂((volume.restrict (Icc (0:ℝ) T)).prod μ),p.1∈Icc (0:ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ha] with p hp
  calc
    ‖fderiv ℝ φ p.2 (X p u)‖≤‖fderiv ℝ φ p.2‖*‖X p u‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖fderiv ℝ φ p.2‖*(C*‖u‖) := mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbound p.1 hp p.2) (norm_nonneg _)))
      (norm_nonneg _)
    _≤D*(C*‖u‖) := mul_le_mul_of_nonneg_right (hDb p.2) (mul_nonneg hC (norm_nonneg _))
    _=D*C*‖u‖ := by ring

theorem gradient_exchange {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X) {T C : ℝ}
    (hC : 0≤C) (hbound : ∀t∈Icc (0:ℝ) T,∀y,‖X (t,y)‖≤C) (u : E) :
    (∫t in Icc (0:ℝ) T,∫y,fderiv ℝ φ y (X (t,y) u) ∂μ)=
      ∫y,fderiv ℝ φ y ((∫t in Icc (0:ℝ) T,X (t,y)) u) ∂μ := by
  rw [integral_integral_swap (gradient_time_space_integrable (μ:=μ) hφ hφc hX hC hbound u)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hi : IntegrableOn (fun t => X (t,y)) (Icc (0:ℝ) T) :=
    (hX.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hh := ((fderiv ℝ φ y).comp (ContinuousLinearMap.apply ℝ E u)).integral_comp_comm hi
  exact hh
end LogConcaveSampling.GradientIntegral

end

end

end

end OAI
