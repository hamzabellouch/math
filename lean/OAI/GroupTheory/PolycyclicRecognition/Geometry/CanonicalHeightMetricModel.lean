import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightIntegration
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # The published Lie-model reduction with its actual canonical height -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

/-- The model reduction, faithful matrix differential, scalar integration
and exponential chart supply a Euclidean canonical height. Metric
compatibility is proved from the selected metric's chain property. No
affine-height estimate is part of these published inputs. -/
theorem exists_canonical_height_metric_model
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (differential : MatrixLieDifferentialInput)
    (dixmier : ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier),
      letI := d.compatibleMetric
      DixmierExponentialInput (E := R.modelSpace) (G := R.carrier))
    (integrate : ∀ R : SimplyConnectedSolvableLieModel,
      ScalarCharacterIntegrationInput (E := R.modelSpace) (G := R.carrier))
    (S : SimplyConnectedSolvableLieModel) :
    ∃ (R : SimplyConnectedSolvableLieModel) (a : ℕ)
      (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
      (dS : ProperChainMetric S.carrier) (dR : ProperChainMetric R.carrier),
      letI := dS.compatibleMetric
      letI := dR.compatibleMetric
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
  obtain ⟨R, a, ⟨T⟩, dS, dR, he⟩ :=
    exists_triangularAdjoint_metric_model ct metric differential S
  refine ⟨R, a, T, dS, dR, ?_⟩
  let := dS.compatibleMetric
  let := dR.compatibleMetric
  let := dR.proper_compatibleMetric
  let := dR.isometric_compatibleMetric
  let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q : HeightSpace T.character ≃ₗ[ℝ] W :=
    LinearEquiv.ofFinrankEq _ _ (by simp [W])
  obtain ⟨Exp, hExp⟩ := (dixmier R dR ⟨a, ⟨T⟩⟩).1
  obtain ⟨π, hπ, hsurj, hquot, K, hK, hLip⟩ :=
    exists_lipschitz_canonical_height T dR.chains_compatibleMetric
      (integrate R) (dixmier R dR) q Exp hExp
  exact ⟨he, q, Exp, π, hExp, hπ, hsurj, hquot, K, hK, hLip⟩

end PolycyclicRecognition

end

end OAI
