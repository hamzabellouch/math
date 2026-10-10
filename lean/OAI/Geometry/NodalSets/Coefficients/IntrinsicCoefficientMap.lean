import OAI.Geometry.NodalSets.Charts.IntrinsicLiftGeometry
import OAI.Geometry.NodalSets.Coefficients.MatrixCoefficientMap

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicChartCoefficient (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) : CoefficientPoint BaseModel :=
  (matrixContravariant (intrinsicSphereChartTensor A p z), ρ ((extChartAt (𝓡 4) p).symm z))

lemma intrinsicChartCoefficient_pair (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z (baseCovectorCoordinates α))
        (sphereCoordinateCovector p z (baseCovectorCoordinates β)) := by
  change α (matrixContravariant _ β) = _
  rw [matrixContravariant_pair,intrinsicSphereChartTensor_eq,intrinsicAmbientMatrix_chart_pairing]

lemma intrinsicChartCovector_apply (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (α : BaseModel →L[ℝ] ℝ) (v : BaseModel) :
    sphereCoordinateCovector p z (baseCovectorCoordinates α)
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z v) = α v := by
  exact (sphereCoordinateCovector_apply p hz (baseCovectorCoordinates α) (WithLp.ofLp v)).trans
    (baseCovectorCoordinates_apply α v).symm

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hs hp in
lemma intrinsicSphereChartTensor_posDef (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : (intrinsicSphereChartTensor A p z).PosDef := by
  rw [intrinsicSphereChartTensor_eq]
  change (frameContravariant _ _).PosDef
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) zero_lt_one p hz
    (intrinsicAmbientMatrix_radial A _),one_smul]
  exact (sphereWeightedChartMatrix_posDef _ (intrinsicAmbientMatrix_posDef A hs hp _)
    zero_lt_one p hz).inv

include hs hp in
lemma intrinsicChartCoefficient_positive (ρ : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) :
    0 < α ((intrinsicChartCoefficient A ρ p z).1 α) :=
  matrixContravariant_positive _ (intrinsicSphereChartTensor_posDef A hs hp p hz) α hα

include hs in
lemma intrinsicChartCoefficient_symmetric (ρ : Base → ℝ) (p : Base) (z : BaseModel)
    (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) = β ((intrinsicChartCoefficient A ρ p z).1 α) := by
  rw [intrinsicChartCoefficient_pair,intrinsicChartCoefficient_pair,hs]

end
end Yau.Target

end OAI
