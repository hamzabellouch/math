import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightRepresentationModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RiemannianExponentialInputs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ControlledContraction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialChartBridge

namespace OAI

/-! # Canonical height and contraction in the published Riemannian metric -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

/-- Choose the Riemannian metric after fixing the triangular model, and
construct its controlled exponential contraction from the two precisely
stated published regularity inputs. -/
theorem exists_canonical_height_model_with_controlled_contraction
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (riemannian : LieRiemannianMetricInput)
    (regular : ∀ R : SimplyConnectedSolvableLieModel,
      DixmierExponentialDiffeomorphismInput (E := R.modelSpace) (G := R.carrier))
    (differential : MatrixLieDifferentialInput)
    (realize : ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier),
      letI := d.compatibleMetric
      ExponentialLinearRealizationInput (EG := R.modelSpace) (G := R.carrier))
    (S : SimplyConnectedSolvableLieModel) :
    ∃ (R : SimplyConnectedSolvableLieModel) (a : ℕ)
      (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a),
      ∃ (dS : ProperChainMetric S.carrier) (dR : ProperMinimizingMetric R.carrier),
        letI := dS.compatibleMetric
        letI := dR.toProperChainMetric.compatibleMetric
        let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
        Nonempty (MetricQuasiEquivalence S.carrier R.carrier) ∧
        Nonempty (ControlledContraction R.carrier) ∧
        ∃ (q : HeightSpace T.character ≃ₗ[ℝ] W)
          (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
          (π : R.carrier →* Multiplicative W),
          IsGroupExponential Exp ∧
          (∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v)) ∧
          Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
          ∃ K : ℝ, 0 ≤ K ∧ ∀ x y,
            ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨R, a, T, hmetrics⟩ :=
    exists_canonical_height_model_of_representation ct metric differential
      (fun R d => by
        let := d.compatibleMetric
        exact (regular R).toTopological) realize S
  obtain ⟨dS⟩ := S.nonempty_properChainMetric metric
  obtain ⟨dR, hcompat⟩ := riemannian R
  refine ⟨R, a, T, dS, dR, ?_⟩
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  obtain ⟨he, q, Exp, π, hExp, hπ, hsurj, hquot, K, hK, hLip⟩ := hmetrics dS dR.toProperChainMetric
  obtain ⟨φ, hφ, hf, hb⟩ := regular R a T Exp hExp
  obtain ⟨hfLip, hbLip⟩ := hcompat _ φ hf hb
  have hφ0 : φ 0 = 1 := by simpa only [map_zero, hExp.map_zero] using hφ 0
  exact ⟨he, ⟨ControlledContraction.ofChart φ hφ0 hfLip hbLip⟩,
    q, Exp, π, hExp, hπ, hsurj, hquot, K, hK, hLip⟩

end PolycyclicRecognition

end

end OAI
