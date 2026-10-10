import Mathlib

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open scoped Pointwise
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The action of a genuine orthogonal coordinate change on the unit sphere. -/
def sphereIsometry (A : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  A.toHomeomorph.subtype (fun x => by simp only [Metric.mem_sphere, dist_zero_right]; exact A.norm_map x |>.symm ▸ Iff.rfl)

theorem sphereIsometry_coe (A : E ≃ₗᵢ[ℝ] E) (e : sphere (0 : E) 1) :
    (sphereIsometry A e : E) = A e := rfl

variable [FiniteDimensional ℝ E]

section
variable [MeasurableSpace E] [BorelSpace E]

/- The round measure, defined by ordinary Euclidean polar coordinates, is
orthogonally invariant in every dimension, including the two-point sphere. -/
theorem sphereIsometry_measurePreserving (A : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry A) volume.toSphere volume.toSphere := by
  refine ⟨(sphereIsometry A).continuous.measurable, ?_⟩
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply (sphereIsometry A).continuous.measurable hT,
    Measure.toSphere_apply' _ ((sphereIsometry A).continuous.measurable hT),
    Measure.toSphere_apply' _ hT]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereIsometry A) ⁻¹' T)) =
      A ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' T)) := by
    ext y
    constructor
    · rintro ⟨r, hr, z, ⟨q,hq,rfl⟩, rfl⟩
      exact ⟨r, hr, A q, ⟨sphereIsometry A q, hq, rfl⟩, by simp⟩
    · rintro ⟨r, hr, z, ⟨q,hq,rfl⟩, hy⟩
      refine ⟨r, hr, A.symm q, ⟨(sphereIsometry A).symm q, ?_, rfl⟩, ?_⟩
      · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hq
      · apply A.injective
        simpa only [map_smul, A.apply_symm_apply] using hy
  rw [hset]
  change volume (A.toHomeomorph ⁻¹' _) = _
  rw [← A.toHomeomorph.measurableEmbedding.map_apply]
  change Measure.map A volume _ = _
  rw [A.measurePreserving.map_eq]

 theorem integral_sphere_isometry (A : E ≃ₗᵢ[ℝ] E)
    (f : sphere (0 : E) 1 → ℝ) :
    (∫ e, f (sphereIsometry A e) ∂volume.toSphere) = ∫ e, f e ∂volume.toSphere :=
  (sphereIsometry_measurePreserving A).integral_comp (sphereIsometry A).measurableEmbedding f

end

/- The infinitesimal generator of rotation in the oriented `u,v` plane. -/
def rotationGenerator (u v : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E u).smulRight v -
    (InnerProductSpace.toDual ℝ E v).smulRight u

def planeProjection (u v : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E u).smulRight u +
    (InnerProductSpace.toDual ℝ E v).smulRight v

def planeRotationMap (u v : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (Real.cos t - 1) • planeProjection u v +
    Real.sin t • rotationGenerator u v

theorem planeRotationMap_apply (u v x : E) (t : ℝ) :
    planeRotationMap u v t x = x +
      ((Real.cos t - 1) * inner ℝ u x - Real.sin t * inner ℝ v x) • u +
      (Real.sin t * inner ℝ u x + (Real.cos t - 1) * inner ℝ v x) • v := by
  simp only [planeRotationMap, planeProjection, rotationGenerator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, sub_apply]
  module

theorem planeRotationMap_inner {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) (x y : E) :
    inner ℝ (planeRotationMap u v t x) (planeRotationMap u v t y) = inner ℝ x y := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  simp only [planeRotationMap_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hu, hv, huv, hvu,
    mul_zero, mul_one, add_zero]
  rw [real_inner_comm x u, real_inner_comm x v]
  linear_combination (inner ℝ x u * inner ℝ u y + inner ℝ x v * inner ℝ v y) *
    (Real.sin_sq_add_cos_sq t)

/- A genuine orthogonal rotation; its formula is the usual two-plane rotation,
not an assumed measure-invariant flow. -/
def planeRotation {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective
    ((planeRotationMap u v t).toLinearMap.isometryOfInner (planeRotationMap_inner hu hv huv t))
    (LinearMap.surjective_of_injective
      ((planeRotationMap u v t).toLinearMap.isometryOfInner
        (planeRotationMap_inner hu hv huv t)).injective)

theorem planeRotation_apply {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) (x : E) :
    planeRotation hu hv huv t x = planeRotationMap u v t x := rfl

theorem planeRotation_zero (u v x : E) : planeRotationMap u v 0 x = x := by
  simp [planeRotationMap]

theorem planeRotation_hasDerivAt (u v x : E) (t : ℝ) :
    HasDerivAt (fun r => planeRotationMap u v r x)
      ((-Real.sin t) • planeProjection u v x + Real.cos t • rotationGenerator u v x) t := by
  have hh := ((hasDerivAt_const t x).add
    (((Real.hasDerivAt_cos t).sub_const 1).smul_const (planeProjection u v x))).add
      ((Real.hasDerivAt_sin t).smul_const (rotationGenerator u v x))
  convert hh using 1
  · funext r; rfl
  · simp

theorem planeRotation_continuous (u v : E) :
    Continuous (fun q : ℝ × E => planeRotationMap u v q.1 q.2) := by
  simp only [planeRotationMap, add_apply, smul_apply, ContinuousLinearMap.id_apply]
  fun_prop

theorem planeRotation_mem_sphere {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0)
    (t : ℝ) (e : sphere (0 : E) 1) :
    planeRotationMap u v t e ∈ sphere (0 : E) 1 := by
  have h := (planeRotation hu hv huv t).norm_map (e : E)
  rw [planeRotation_apply] at h
  rw [mem_sphere, dist_zero_right, h]
  exact mem_sphere_zero_iff_norm.mp e.property

theorem planeRotation_sphere_continuous (u v : E) :
    Continuous (fun p : ℝ × sphere (0 : E) 1 => planeRotationMap u v p.1 p.2) := by
  simp only [planeRotationMap, add_apply, smul_apply, ContinuousLinearMap.id_apply]
  fun_prop

/- Differentiation under a finite measure on a compact parameter space.
The uniform bound is proved, rather than supplied as an analytic assumption. -/
theorem hasDerivAt_integral_compact {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F D : ℝ → α → ℝ}
    (hF : Continuous (fun p : ℝ × α => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × α => D p.1 p.2))
    (hd : ∀ t a, HasDerivAt (fun r => F r a) (D t a) t) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, D 0 a ∂μ) 0 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_univ (X := α))).exists_bound_of_continuousOn
    (f := fun p : ℝ × α => D p.1 p.2) hD.continuousOn
  have hFc (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hDc (t : ℝ) : Continuous (D t) := hD.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := μ) (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := fun _ => C)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall (fun t => (hFc t).aestronglyMeasurable))
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDc 0).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e t ht => hC (t,e) ⟨ht, mem_univ e⟩))
    (integrable_const C) (Filter.Eventually.of_forall (fun e t _ => hd t e))).2

variable [MeasurableSpace E] [BorelSpace E]

/- Infinitesimal orthogonal invariance of the actual round measure. This is
proved by differentiating the genuine rotation, with a compact-sphere bound. -/
theorem integral_sphere_rotation_deriv {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    (∫ e : sphere (0 : E) 1, fderiv ℝ f e (rotationGenerator u v e)
      ∂volume.toSphere) = 0 := by
  let F : ℝ → sphere (0 : E) 1 → ℝ := fun t e => f (planeRotationMap u v t e)
  let D : ℝ → sphere (0 : E) 1 → ℝ := fun t e =>
    fderiv ℝ f (planeRotationMap u v t e)
      ((-Real.sin t) • planeProjection u v e + Real.cos t • rotationGenerator u v e)
  have hR := planeRotation_mem_sphere hu hv huv
  have hRc := planeRotation_sphere_continuous u v
  have hFc : Continuous (fun p : ℝ × sphere (0 : E) 1 => F p.1 p.2) :=
    hf.continuousOn.comp_continuous hRc (fun p => hSU (hR p.1 p.2))
  have hDc : Continuous (fun p : ℝ × sphere (0 : E) 1 => D p.1 p.2) := by
    have hfd : Continuous (fun p : ℝ × sphere (0 : E) 1 =>
        fderiv ℝ f (planeRotationMap u v p.1 p.2)) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact ((hf.contDiffAt (hU.mem_nhds (hSU (hR p.1 p.2)))).continuousAt_fderiv (by simp)).comp
        (f := fun q : ℝ × sphere (0 : E) 1 => planeRotationMap u v q.1 q.2)
        hRc.continuousAt
    apply hfd.clm_apply
    change Continuous (fun p : ℝ × sphere (0 : E) 1 =>
      (-Real.sin p.1) • planeProjection u v (p.2 : E) +
      Real.cos p.1 • rotationGenerator u v (p.2 : E))
    exact ((Real.continuous_sin.comp continuous_fst).neg.smul
      ((planeProjection u v).continuous.comp (continuous_subtype_val.comp continuous_snd))).add
      ((Real.continuous_cos.comp continuous_fst).smul
      ((rotationGenerator u v).continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hdiff (t : ℝ) (e : sphere (0 : E) 1) : HasDerivAt (fun r => F r e) (D t e) t :=
    ((hf.contDiffAt (hU.mem_nhds (hSU (hR t e)))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      t (planeRotation_hasDerivAt u v e t)
  have hdint := hasDerivAt_integral_compact (μ := volume.toSphere) hFc hDc hdiff
  have hconst : (fun t => ∫ e, F t e ∂volume.toSphere) =
      (fun _ : ℝ => ∫ e : sphere (0 : E) 1, f e ∂volume.toSphere) := by
    funext t
    exact integral_sphere_isometry (planeRotation hu hv huv t) (fun e => f e)
  have hzero := hdint
  rw [hconst] at hzero
  have hz := hzero.unique (hasDerivAt_const (0 : ℝ) _)
  simpa only [D, planeRotation_zero, Real.sin_zero, neg_zero, zero_smul,
    Real.cos_zero, one_smul, zero_add] using hz

end AffineBernstein

end

end OAI
