import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightMetricChoice
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MinimizingLieMetric

namespace OAI

/-! # Canonical height in the published minimizing metric -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

/-- Choose the published minimizing metric only after the triangular Lie
model is fixed. Its chain structure is derived by sampling those paths. -/
theorem exists_canonical_height_model_with_minimizing_metric
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (minimizing : LieMinimizingMetricInput)
    (differential : MatrixLieDifferentialInput)
    (dixmier : ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier),
      letI := d.compatibleMetric
      DixmierExponentialInput (E := R.modelSpace) (G := R.carrier))
    (integrate : ∀ R : SimplyConnectedSolvableLieModel,
      ScalarCharacterIntegrationInput (E := R.modelSpace) (G := R.carrier))
    (S : SimplyConnectedSolvableLieModel) :
    ∃ (R : SimplyConnectedSolvableLieModel) (a : ℕ)
      (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a),
      ∃ (dS : ProperChainMetric S.carrier) (dR : ProperMinimizingMetric R.carrier),
        letI := dS.compatibleMetric
        letI := dR.toProperChainMetric.compatibleMetric
        let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
        Nonempty (MetricQuasiEquivalence S.carrier R.carrier) ∧
        ∃ (q : HeightSpace T.character ≃ₗ[ℝ] W)
          (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
          (π : R.carrier →* Multiplicative W),
          IsGroupExponential Exp ∧
          (∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v)) ∧
          Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
          ∃ K : ℝ, 0 ≤ K ∧ ∀ x y,
            ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨R, a, T, hmetrics⟩ :=
    exists_canonical_height_model_with_metric_choice ct metric differential dixmier integrate S
  obtain ⟨dS⟩ := S.nonempty_properChainMetric metric
  obtain ⟨dR⟩ := minimizing R
  exact ⟨R, a, T, dS, dR, hmetrics dS dR.toProperChainMetric⟩

end PolycyclicRecognition

end

end OAI
