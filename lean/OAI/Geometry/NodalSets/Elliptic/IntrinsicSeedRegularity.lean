import OAI.Geometry.NodalSets.Charts.SeedChartOperator
import OAI.Geometry.NodalSets.Charts.SeedCoordMetricRegularity
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_regular (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ContDiff ℝ ∞ (intrinsicSeedCoordMetric A rho) ∧
    (∀ x u v, intrinsicSeedCoordMetric A rho x u v = intrinsicSeedCoordMetric A rho x v u) ∧
    (∀ x v, v ≠ 0 → 0 < intrinsicSeedCoordMetric A rho x v v) := by
  rw [← intrinsicSeedCoordMetric_eq A hs hp rho hrp]
  let c := intrinsicChartCoefficient A rho seedPoint
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr (fun z ↦
    intrinsicChartCoefficient_smoothAt A hA hs hp rho hr seedPoint
      (by rw [centeredSphereChart_target]; trivial))
  have hcp : ∀ z (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c z).1 α) :=
    fun z ↦ intrinsicChartCoefficient_positive A hs hp rho seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  exact ⟨seedCoordMetric_smooth c hc hcp,
    seedCoordMetric_symmetric c hcp (fun z ↦ intrinsicChartCoefficient_symmetric A hs rho seedPoint z),
    seedCoordMetric_positive c hcp (fun _ ↦ hrp _)⟩

lemma intrinsicSeedCoord_residual (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x) (N : ℕ) (x : Coord) :
    sourceWeightedOperator (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun z ↦ (seedCoordinateField N z:ℂ)) x+
        (seedEigenvalue N:ℂ)*(seedCoordinateField N x:ℂ) =
      (intrinsicWeightedChartOperator A rho (sphericalSeed N) seedPoint (seedCoordEquiv x)+
        seedEigenvalue N*sphericalSeed N
          ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) := by
  have he : seedCoordinateField N = fun z ↦ sphericalSeed N
      ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)) := funext (seedCoordinateField_literal N)
  rw [he,intrinsicSeedCoordOperator A hA hs hp rho hrp _ (sphericalSeed_smooth N)]

end
end Yau.Target

end OAI
