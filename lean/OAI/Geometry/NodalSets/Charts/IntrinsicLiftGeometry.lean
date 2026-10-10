import OAI.Geometry.NodalSets.Elliptic.IntrinsicWeightedLift
import OAI.Geometry.NodalSets.Elliptic.TargetWeightedVolume

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

include hs hp hrp in
lemma intrinsic_horizontal_inverse (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    (sphereWeightedChartMatrix (intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z))
      (rho ((extChartAt (𝓡 4) p).symm z)) p z)⁻¹ =
      (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ • intrinsicSphereChartTensor A p z := by
  rw [intrinsicSphereChartTensor_eq]
  change _ = _ • Yau.Geometry.frameContravariant _ _
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) (hrp _) p hz
    (intrinsicAmbientMatrix_radial A _), smul_smul, inv_mul_cancel₀ (hrp _).ne', one_smul]

include hs hp hrp in
lemma intrinsic_circle_ratio (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ambientCircleWeight (intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z))
      (rho ((extChartAt (𝓡 4) p).symm z)) =
      rho ((extChartAt (𝓡 4) p).symm z) /
        (Real.sqrt (sphereWeightedChartMatrix
          (intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z))
          (rho ((extChartAt (𝓡 4) p).symm z)) p z).det /
            Real.sqrt (sphereRoundChartMatrix p z).det) :=
  ambientCircleWeight_chart_ratio _ (intrinsicAmbientMatrix_posDef A hs hp _) (hrp _) p hz
    (intrinsicAmbientMatrix_radial A _)

lemma intrinsicWeightedMetric_volume (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    volumeFactor (intrinsicWeightedMetric A hA hs hp rho hr hrp) (extChartAt modelWithCorners p) y =
      targetFrameVolume * (rho ((extChartAt (𝓡 4) p.1).symm y.1) *
        Real.sqrt (sphereRoundChartMatrix p.1 y.1).det * Real.sqrt (circleChartFactor p.2 y.2)) :=
  independentAmbientMetric_target_volume (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (intrinsicAmbientMatrix_radial A) p hy

lemma intrinsicWeightedMetric_eigenfunction (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (hf0 : f ≠ 0) (lam : ℝ)
    (he : ∀ x : Base, -intrinsicWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam * f x) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (intrinsicWeightedMetric A hA hs hp rho hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam * circleLift f x := by
  apply independentAmbientMetric_eigenfunction_lift (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (intrinsicAmbientMatrix_radial A) f hf hf0 lam
  intro x
  simpa only [intrinsicWeightedChartOperator_eq] using he x

end
end Yau.Target

end OAI
