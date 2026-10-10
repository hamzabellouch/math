import OAI.Geometry.NodalSets.Charts.FrameCotangent
import OAI.Geometry.NodalSets.Elliptic.WeightedLift

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma sphereChartTensor_pullback (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) :
    sphereChartTensor A p z = frameLeftInverse (sphereChartFrame p z) *
      A ((extChartAt (𝓡 4) p).symm z) * (frameLeftInverse (sphereChartFrame p z)).transpose :=
  frameContravariant_pullback _ _

lemma sphereChart_covector_representative (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 4 → ℝ) :
    (sphereChartFrame p z).transpose *ᵥ
      ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) = v :=
  frameLeftInverse_covector _ (sphereChartFrame_injective p hz) v

lemma sphereChartTensor_pairing (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) (v w : Fin 4 → ℝ) :
    v ⬝ᵥ (sphereChartTensor A p z *ᵥ w) =
      ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) ⬝ᵥ
        (A ((extChartAt (𝓡 4) p).symm z) *ᵥ
          ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ w)) := by
  rw [sphereChartTensor_pullback,← mulVec_mulVec,← mulVec_mulVec]
  rw [dotProduct_mulVec,← mulVec_transpose]

end
end Yau.Target

end OAI
