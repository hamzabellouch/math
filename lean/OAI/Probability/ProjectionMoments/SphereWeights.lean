import OAI.Probability.ProjectionMoments.Asymptotics

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace ProjectionMoments
open NoiselessRegression
variable {d : ℕ}

def extendSphereWeight (f : UnitSphere d → ℝ≥0∞) : Vector d → ℝ≥0∞ :=
  Function.extend Subtype.val f (fun _ => 0)

@[simp] lemma extendSphereWeight_val (f : UnitSphere d → ℝ≥0∞) (s : UnitSphere d) :
    extendSphereWeight f s.val = f s :=
  Subtype.val_injective.extend_apply f (fun _ => 0) s

lemma measurable_extendSphereWeight {f : UnitSphere d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (extendSphereWeight f) :=
  (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).measurable_extend hf measurable_const

lemma extendSphereWeight_le_one {f : UnitSphere d → ℝ≥0∞} (hf : ∀ s, f s ≤ 1) :
    ∀ x, extendSphereWeight f x ≤ 1 := by
  intro x
  by_cases hx : ∃ s : UnitSphere d, s.val = x
  · obtain ⟨s,rfl⟩ := hx
    simpa using hf s
  · rw [extendSphereWeight,Function.extend_apply' _ _ _ hx]
    exact zero_le_one

lemma sphereWeight_measure (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    ambientSphereLaw.withDensity (extendSphereWeight f) =
      ((uniformSphere d).withDensity f).map Subtype.val := by
  ext S hS
  rw [withDensity_apply _ hS,Measure.map_apply measurable_subtype_coe hS,
    withDensity_apply _ (measurable_subtype_coe hS)]
  change (∫⁻ x in S, extendSphereWeight f x ∂(uniformSphere d).map Subtype.val) = _
  rw [← lintegral_indicator hS,lintegral_map ((measurable_extendSphereWeight hf).indicator hS)
      measurable_subtype_coe,← lintegral_indicator (measurable_subtype_coe hS)]
  apply lintegral_congr
  intro s
  by_cases hs : s.val ∈ S <;> simp [hs,extendSphereWeight_val]

lemma sphereWeight_potential (α : ℝ) (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    rieszPotential α (extendSphereWeight f) =
      ⨆ z : Vector d, ∫⁻ s, f s * (ENNReal.ofReal ‖s.val-z‖)^(-α) ∂uniformSphere d := by
  unfold rieszPotential
  congr 1
  funext z
  change (∫⁻ x, extendSphereWeight f x*rieszKernel α z x ∂(uniformSphere d).map Subtype.val) = _
  rw [lintegral_map (show Measurable (fun x => extendSphereWeight f x*rieszKernel α z x) from
    (measurable_extendSphereWeight hf).mul (measurable_rieszKernel α z)) measurable_subtype_coe]
  apply lintegral_congr
  intro s
  simp only [extendSphereWeight_val,rieszKernel]

lemma sphereWeight_restriction (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (H : Set (UnitSphere d)) (hH : MeasurableSet H) :
    sphereWeightedRestriction (extendSphereWeight f) (Subtype.val '' H) =
      (((uniformSphere d).withDensity f).restrict H).map Subtype.val := by
  have he := MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet :
    MeasurableSet (Metric.sphere (0 : Vector d) 1))
  rw [sphereWeightedRestriction,sphereWeight_measure f hf,Measure.restrict_map measurable_subtype_coe
    (he.measurableSet_image.mpr hH)]
  congr 1
  congr 1
  exact Set.preimage_image_eq _ Subtype.val_injective

lemma sphere_weight_representation (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (hf1 : ∀ s, f s ≤ 1) :
    ∃ F : Vector d → ℝ≥0∞, Measurable F ∧ (∀ x, F x ≤ 1) ∧
      (∀ s : UnitSphere d, F s.val = f s) ∧
      ambientSphereLaw.withDensity F = ((uniformSphere d).withDensity f).map Subtype.val :=
  ⟨extendSphereWeight f,measurable_extendSphereWeight hf,extendSphereWeight_le_one hf1,
    extendSphereWeight_val f,sphereWeight_measure f hf⟩

end ProjectionMoments
end

end

end OAI
