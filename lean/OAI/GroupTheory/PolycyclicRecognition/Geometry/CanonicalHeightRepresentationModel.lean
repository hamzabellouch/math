import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightFromRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TriangulableMetricChoice
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLieDifferential

namespace OAI

/-! # Choosing the Lie model and its canonical height from representation data -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

theorem exists_canonical_height_model_of_representation
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (differential : MatrixLieDifferentialInput)
    (dixmier : ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier),
      letI := d.compatibleMetric
      DixmierExponentialInput (E := R.modelSpace) (G := R.carrier))
    (realize : ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier),
      letI := d.compatibleMetric
      ExponentialLinearRealizationInput (EG := R.modelSpace) (G := R.carrier))
    (S : SimplyConnectedSolvableLieModel) :
    ∃ (R : SimplyConnectedSolvableLieModel) (a : ℕ)
      (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a),
      ∀ (dS : ProperChainMetric S.carrier) (dR : ProperChainMetric R.carrier),
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
  obtain ⟨R, hR, hmetrics⟩ :=
    exists_realTriangulable_model_with_metric_choice ct metric S
  obtain ⟨a, ⟨T⟩⟩ := IsRealTriangulable.exists_triangularAdjoint differential R hR
  refine ⟨R, a, T, ?_⟩
  intro dS dR
  let := dS.compatibleMetric
  let := dR.compatibleMetric
  let := dR.proper_compatibleMetric
  let := dR.isometric_compatibleMetric
  let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q : HeightSpace T.character ≃ₗ[ℝ] W :=
    LinearEquiv.ofFinrankEq _ _ (by simp [W])
  obtain ⟨Exp, hExp⟩ := (dixmier R dR ⟨a, ⟨T⟩⟩).1
  obtain ⟨π, hπ, hsurj, hquot, K, hK, hLip⟩ :=
    exists_lipschitz_canonical_height_of_representation T dR.chains_compatibleMetric
      (dixmier R dR) (realize R dR) q Exp hExp
  exact ⟨hmetrics dS dR, q, Exp, π, hExp, hπ, hsurj, hquot, K, hK, hLip⟩

end PolycyclicRecognition

end

end OAI
