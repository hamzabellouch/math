import Mathlib
import OAI.Probability.SphericalField.Perceptron.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
section SphereInvariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereIsometryMap (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 := ⟨e x, by simp⟩

omit [FiniteDimensional ℝ E] in
lemma sphereIsometryMap_measurable (e : E ≃ₗᵢ[ℝ] E) : Measurable (sphereIsometryMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sphereIsometryMap_preimage_cone (e : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereIsometryMap e ⁻¹' s)) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨r,hr,e u,⟨sphereIsometryMap e u,hu,rfl⟩,by simp⟩
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,he⟩
    refine ⟨r,hr,e.symm u,⟨sphereIsometryMap e.symm u,?_,rfl⟩,?_⟩
    · simpa [sphereIsometryMap] using hu
    · apply e.injective
      simpa only [map_smul,LinearIsometryEquiv.apply_symm_apply] using he

lemma sphereIsometryMap_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometryMap e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometryMap_measurable e) hs,
    Measure.toSphere_apply' _ ((sphereIsometryMap_measurable e) hs),Measure.toSphere_apply' _ hs,
    sphereIsometryMap_preimage_cone]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end SphereInvariance

lemma unitSphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving (sphereIsometryMap e) (unitSphereLaw N) (unitSphereLaw N) := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  simp only [unitSphereLaw,Measure.map_smul _ (sphereIsometryMap_measurable e).aemeasurable]
  rw [(sphereIsometryMap_preserving e).map_eq]

lemma sphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving e (sphereLaw N) (sphereLaw N) := by
  refine ⟨e.continuous.measurable,?_⟩
  have hm : Measurable (fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) :=
    (continuous_subtype_val.const_smul (Real.sqrt (N:ℝ))).measurable
  rw [sphereLaw,Measure.map_map e.continuous.measurable hm]
  have hc : (e ∘ fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) =
      (fun x : Metric.sphere (0 : Spin N) 1 => Real.sqrt (N:ℝ) • x.val) ∘ sphereIsometryMap e := by
    funext x
    exact e.map_smul _ _
  rw [hc]
  rw [← Measure.map_map hm (sphereIsometryMap_measurable e),
    (unitSphereLaw_isometry_preserving e).map_eq]

end SphericalPerceptron
end
end
end

end OAI
