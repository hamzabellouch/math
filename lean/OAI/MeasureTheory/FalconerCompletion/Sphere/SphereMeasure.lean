import Mathlib

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def canonicalSphereMeasureND (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Measure V :=
  Measure.map Subtype.val (volume : Measure V).toSphere

lemma canonicalSphereMeasureND_apply {s : Set V} (hs : MeasurableSet s) :
    canonicalSphereMeasureND V s = (Module.finrank ℝ V : ℝ≥0∞) *
      volume (Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ s)) := by
  rw [canonicalSphereMeasureND, Measure.map_apply measurable_subtype_coe hs,
    Measure.toSphere_apply' volume (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp

lemma canonicalSphereMeasureND_linearIsometry (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving e (canonicalSphereMeasureND V) (canonicalSphereMeasureND V) := by
  refine ⟨e.continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    canonicalSphereMeasureND_apply (e.continuous.measurable hs),
    canonicalSphereMeasureND_apply hs]
  have hset : Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,rfl⟩
      exact ⟨r,hr,e w,⟨by simpa using hw,hsw⟩,by simp⟩
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,hwx⟩
      refine ⟨r,hr,e.symm w,⟨by simpa using hw,by simpa using hsw⟩,?_⟩
      apply e.injective
      simpa using hwx
  rw [hset, e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

lemma integral_canonicalSphereMeasureND_isometry (e : V ≃ₗᵢ[ℝ] V) (f : V → ℂ) :
    (∫ w, f (e w) ∂canonicalSphereMeasureND V) = ∫ w, f w ∂canonicalSphereMeasureND V :=
  (canonicalSphereMeasureND_linearIsometry e).integral_comp e.toHomeomorph.measurableEmbedding f

lemma integral_canonicalSphereMeasureND_neg (f : V → ℂ) :
    (∫ w, f (-w) ∂canonicalSphereMeasureND V) = ∫ w, f w ∂canonicalSphereMeasureND V :=
  integral_canonicalSphereMeasureND_isometry (LinearIsometryEquiv.neg ℝ) f

lemma integrable_canonicalSphereMeasureND {f : V → ℂ} (hf : Continuous f) :
    Integrable f (canonicalSphereMeasureND V) := by
  rw [canonicalSphereMeasureND,
    integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable]
  exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

instance canonicalSphereMeasureND_finite : IsFiniteMeasure (canonicalSphereMeasureND V) := by
  unfold canonicalSphereMeasureND
  infer_instance

lemma canonicalSphereMeasureND_ae_norm :
    ∀ᵐ w ∂canonicalSphereMeasureND V, ‖w‖ = 1 := by
  rw [canonicalSphereMeasureND, ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  exact Filter.Eventually.of_forall (fun w => by simp)

omit [MeasurableSpace V] [BorelSpace V] in
noncomputable def skewFlowND (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) : V ≃ₗᵢ[ℝ] V := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) := .restrictScalars ℚ ℝ (V →L[ℝ] V)
  exact Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • A),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff,star_smul,hA]
      simp)⟩

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_apply (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) (w : V) :
    skewFlowND A hA t w = NormedSpace.exp (t • A) w := rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_zero (A : V →L[ℝ] V) (hA : star A = -A) (w : V) :
    skewFlowND A hA 0 w = w := by simp [skewFlowND_apply]

omit [MeasurableSpace V] [BorelSpace V] in
lemma skewFlowND_hasDerivAt (A : V →L[ℝ] V) (hA : star A = -A) (t : ℝ) (w : V) :
    HasDerivAt (fun s => skewFlowND A hA s w) (A (skewFlowND A hA t w)) t := by
  simpa only [skewFlowND_apply, mul_apply_eq_comp,
    ContinuousLinearMap.map_zero,add_zero] using
    (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t w)

theorem integral_sphere_skew_derivative_zero (A : V →L[ℝ] V) (hA : star A = -A)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∫ w, fderiv ℝ f w (A w) ∂canonicalSphereMeasureND V) = 0 := by
  let F : ℝ → V → ℂ := fun t w => f (skewFlowND A hA t w)
  let F' : ℝ → V → ℂ := fun t w =>
    fderiv ℝ f (skewFlowND A hA t w) (A (skewFlowND A hA t w))
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:V) 1).exists_bound_of_continuousOn hdf.continuousOn
  have hF' (t : ℝ) : Continuous (F' t) := by
    dsimp [F']
    exact (hdf.comp (skewFlowND A hA t).continuous).clm_apply
      (A.continuous.comp (skewFlowND A hA t).continuous)
  have hbound : ∀ᵐ w ∂canonicalSphereMeasureND V, ∀ t ∈ (Set.univ : Set ℝ),
      ‖F' t w‖ ≤ C*‖A‖ := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw t _
    have hx : ‖skewFlowND A hA t w‖ = 1 := by simpa using hw
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    calc
      ‖fderiv ℝ f (skewFlowND A hA t w)‖ * ‖A (skewFlowND A hA t w)‖ ≤
          ‖fderiv ℝ f (skewFlowND A hA t w)‖ * ‖A‖ :=
        mul_le_mul_of_nonneg_left (by simpa [hx] using A.le_opNorm (skewFlowND A hA t w)) (norm_nonneg _)
      _ ≤ C*‖A‖ := mul_le_mul_of_nonneg_right
        (hC _ (by simpa using hx)) (norm_nonneg _)
  have hdiff : ∀ᵐ w ∂canonicalSphereMeasureND V, ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (F · w) (F' t w) t := by
    filter_upwards [] with w t _
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (skewFlowND_hasDerivAt A hA t w)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := (0:ℝ)) (μ := canonicalSphereMeasureND V) (F := F) (F' := F')
    (bound := fun _ => C*‖A‖) Filter.univ_mem
    (Filter.Eventually.of_forall (fun t =>
      ((hf.continuous.comp (skewFlowND A hA t).continuous).aestronglyMeasurable)))
    (integrable_canonicalSphereMeasureND (hf.continuous.comp (skewFlowND A hA 0).continuous))
    (hF' 0).aestronglyMeasurable hbound (integrable_const _) hdiff
  have he : (fun t => ∫ w, F t w ∂canonicalSphereMeasureND V) =
      (fun _ : ℝ => ∫ w, f w ∂canonicalSphereMeasureND V) := by
    funext t
    exact integral_canonicalSphereMeasureND_isometry (skewFlowND A hA t) f
  have hz := hparam.2
  rw [he] at hz
  have hh := hz.unique (hasDerivAt_const (0:ℝ) (∫ w, f w ∂canonicalSphereMeasureND V))
  simpa [F',skewFlowND_zero] using hh

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def angularDerivativeND (A : V →L[ℝ] V) (f : V → ℂ) (x : V) : ℂ :=
  fderiv ℝ f x (A x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_contDiff (A : V →L[ℝ] V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angularDerivativeND A f) :=
  (hf.fderiv_right (by simp)).clm_apply A.contDiff

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_mul (A : V →L[ℝ] V) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : V) :
    angularDerivativeND A (fun w => f w*g w) x =
      angularDerivativeND A f x*g x + f x*angularDerivativeND A g x := by
  unfold angularDerivativeND
  change (fderiv ℝ (f*g) x) (A x) = _
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [mul_comm,add_comm]

lemma sphere_angular_integration_by_parts (A : V →L[ℝ] V) (hA : star A = -A)
    {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (∫ w, angularDerivativeND A f w*g w ∂canonicalSphereMeasureND V) =
      -(∫ w, f w*angularDerivativeND A g w ∂canonicalSphereMeasureND V) := by
  have hz := integral_sphere_skew_derivative_zero A hA (hf.mul hg)
  change (∫ w, angularDerivativeND A (fun w => f w*g w) w ∂canonicalSphereMeasureND V) = 0 at hz
  simp_rw [angularDerivativeND_mul A hf hg] at hz
  rw [integral_add (f := fun w => angularDerivativeND A f w*g w)
    (g := fun w => f w*angularDerivativeND A g w)
    (integrable_canonicalSphereMeasureND ((angularDerivativeND_contDiff A hf).continuous.mul hg.continuous))
    (integrable_canonicalSphereMeasureND (hf.continuous.mul (angularDerivativeND_contDiff A hg).continuous))] at hz
  exact eq_neg_of_add_eq_zero_left hz

end Attempt4FullFar
end
end

end OAI
