import Mathlib

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

abbrev UnitSphere := Metric.sphere (0 : V) 1

noncomputable def sphereProbability : Measure (UnitSphere V) :=
  ((volume : Measure V).toSphere Set.univ)⁻¹ • volume.toSphere

instance sphereMeasure_neZero : NeZero ((volume : Measure V).toSphere) := by
  constructor
  exact (Measure.toSphere_eq_zero_iff_finrank volume).not.mpr
    (ne_of_gt (Module.finrank_pos (R := ℝ) (M := V)))

instance sphereProbability_isProbability : IsProbabilityMeasure (sphereProbability V) := by
  unfold sphereProbability
  infer_instance

instance sphereProbability_openPos : (sphereProbability V).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul volume.toSphere (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

variable {V}

noncomputable def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : UnitSphere V ≃ₜ UnitSphere V :=
  e.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])

omit [Nontrivial V] in
lemma sphereRotation_preserves_toSphere (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) volume.toSphere volume.toSphere := by
  refine ⟨(sphereRotation e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, e u, ⟨sphereRotation e u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, he⟩
      refine ⟨r, hr, e.symm u, ⟨(sphereRotation e).symm u, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply e.injective
        simpa using he
  rw [hset]
  have he := e.measurePreserving.map_eq
  have hm := e.toMeasurableEquiv.measurableEmbedding.map_apply volume
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at hm
  rw [he] at hm
  exact hm.symm

omit [Nontrivial V] in
lemma sphereRotation_preserves_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) (sphereProbability V) (sphereProbability V) := by
  exact (sphereRotation_preserves_toSphere e).smul_measure _

omit [Nontrivial V] in
lemma integral_sphere_rotation (e : V ≃ₗᵢ[ℝ] V) (g : UnitSphere V → ℝ) :
    (∫ x, g (sphereRotation e x) ∂sphereProbability V) =
      ∫ x, g x ∂sphereProbability V :=
  (sphereRotation_preserves_probability e).integral_comp
    (sphereRotation e).measurableEmbedding g

end SphereMeasure

end BorsukNine

end OAI
