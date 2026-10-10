import OAI.Geometry.NodalSets.Charts.MatrixMetricPullback
import OAI.Geometry.NodalSets.Elliptic.SeedCoordAdmissibility

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def intrinsicSeedCoordMetric (A : IntrinsicTensor) (ρ : Base → ℝ) :
    Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ :=
  linearMetricField seedCoordEquiv
    (fun z ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ seedPoint z))

lemma intrinsicSeedCoordMetric_eq (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x) :
    seedCoordMetric (intrinsicChartCoefficient A ρ seedPoint) = intrinsicSeedCoordMetric A ρ := by
  funext x
  change linearMetricPull seedCoordEquiv _ = linearMetricPull seedCoordEquiv _
  rw [Function.comp_apply,intrinsicChartCoefficient_metric A hs hp ρ hρ seedPoint
    (by rw [centeredSphereChart_target]; trivial)]

lemma intrinsicSeedCoordMetric_apply (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x)
    (x u v : Coord) :
    intrinsicSeedCoordMetric A ρ x u v =
      ambientMatrixForm (weightedBaseMatrix
        (intrinsicAmbientMatrix A ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)))
        (ρ ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x))))
        (sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv u))
        (sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv v)) := by
  change matrixCovariant _ _ _ = _
  rw [show baseChartMetric (intrinsicAmbientMatrix A) ρ seedPoint (seedCoordEquiv x) =
    sphereWeightedChartMatrix _ _ _ _ from rfl,
    matrixCovariant_horizontal _ (intrinsicAmbientMatrix_posDef A hs hp _) _ (hρ _)]
  rfl

theorem seed_envelope_intrinsic_Coord_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (seedCoordinateCube a) ∧ seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) →
      (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ (ρ : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ x : Coord, seedCoordEquiv x ∈ closedBall (0 : BaseModel) r →
        let g := intrinsicSeedCoordMetric A ρ
        let p := metricGradient g seedCoordReal x
        let H := sourceHessian g seedCoordReal x
        (∀ v : Coord, v ≠ 0 → 0 < g x v v) ∧ p ≠ 0 ∧
        ∃ t : Coord, g x p t = 0 ∧ g x t t = 1 ∧
          0 < H p p + (g x p p+4)*H t t := by
  obtain ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,hpatch⟩ := seed_envelope_Coord_patch
  refine ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,?_⟩
  intro A hA hs hp ρ hρ hρp hclose x hx
  have hc := hpatch (intrinsicChartCoefficient A ρ seedPoint)
    (fun y _ ↦ (intrinsicChartCoefficient_smoothAt A hA hs hp ρ hρ seedPoint
      (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp))
    (fun y _ ↦ intrinsicChartCoefficient_positive A hs hp ρ seedPoint
      (by rw [centeredSphereChart_target]; trivial))
    (fun y _ ↦ hρp _) hclose x hx
  simpa only [intrinsicSeedCoordMetric_eq A hs hp ρ hρp] using hc

end
end Yau.Target

end OAI
