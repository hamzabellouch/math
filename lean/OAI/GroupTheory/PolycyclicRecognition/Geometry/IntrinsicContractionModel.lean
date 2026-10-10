import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightContractionModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicSmoothCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHomExt

namespace OAI

/-! # The height model and its contraction without a published global chart -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

theorem exists_intrinsic_height_model_with_controlled_contraction
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (riemannian : LieRiemannianMetricInput) (differential : MatrixLieDifferentialInput)
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
  obtain ⟨R, hR, hmetrics⟩ := exists_realTriangulable_model_with_metric_choice ct metric S
  obtain ⟨a, ⟨T⟩⟩ := IsRealTriangulable.exists_triangularAdjoint differential R hR
  obtain ⟨dS⟩ := S.nonempty_properChainMetric metric
  obtain ⟨dR, hcompat⟩ := riemannian R
  refine ⟨R, a, T, dS, dR, ?_⟩
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q : HeightSpace T.character ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq _ _ (by simp [W])
  let Exp := groupExponential (E := R.modelSpace) (G := R.carrier)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨π, hπ, he, hsurj, hquot, _⟩ := exists_intrinsic_canonical_height T q hExp
  obtain ⟨K, hK, hLip⟩ := continuous_height_lipschitz
    dR.toProperChainMetric.chains_compatibleMetric π hπ
  obtain ⟨n, φ, hφ0, hf, hb⟩ := exists_intrinsic_smooth_coordinates T q Exp hExp π hπ he
  obtain ⟨hfLip, hbLip⟩ := hcompat n φ hf hb
  exact ⟨hmetrics dS dR.toProperChainMetric,
    ⟨ControlledContraction.ofChart φ hφ0 hfLip hbLip⟩,
    q, Exp, π, hExp, he, hsurj, hquot, K, hK, hLip⟩

end PolycyclicRecognition

end

end OAI
