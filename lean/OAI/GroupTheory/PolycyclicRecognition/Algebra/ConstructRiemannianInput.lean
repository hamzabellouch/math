import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructMinimizingLieMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIntoRiemannian
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFromRiemannian
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RiemannianExponentialInputs

namespace OAI

/-! # Discharging the Riemannian metric and coordinate-regularity input -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

theorem lieRiemannianMetricInput : LieRiemannianMetricInput := by
  intro S
  let groupTopology : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ∞
  let localCompact : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  let e : S.modelSpace ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S.modelSpace)) :=
    (Module.finBasis ℝ S.modelSpace).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ S.modelSpace)) ℝ).symm
  refine ⟨leftRiemannianMinimizingMetric e, ?_⟩
  rw [ProperChainMetric.compatibleMetric_eq]
  change letI := leftRiemannianMetric (G := S.carrier) e
    ∀ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ S.carrier),
      ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, S.modelSpace)) ∞ φ →
      ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm →
      LocallyLipschitz φ ∧ LocallyLipschitz φ.symm
  let metric := leftRiemannianMetric (G := S.carrier) e
  intro n φ hφ hφinv
  exact ⟨smooth_into_leftRiemannian_locallyLipschitz e hφ,
    smooth_from_leftRiemannian_locallyLipschitz e hφinv⟩

end PolycyclicRecognition

end

end OAI
