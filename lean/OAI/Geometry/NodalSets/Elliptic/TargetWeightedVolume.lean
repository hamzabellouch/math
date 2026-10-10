import OAI.Geometry.NodalSets.Charts.ProductChartVolume
import OAI.Geometry.NodalSets.Charts.TargetChartBasis

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff
noncomputable section
variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
include hrad

lemma independentAmbientMetric_target_volume (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    volumeFactor (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p) y =
      targetFrameVolume * (rho ((extChartAt (𝓡 4) p.1).symm y.1) *
        Real.sqrt (sphereRoundChartMatrix p.1 y.1).det * Real.sqrt (circleChartFactor p.2 y.2)) := by
  rw [volumeFactor_basis_change,independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy]

lemma independentAmbientMetric_target_volume_pos (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    0 < volumeFactor (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p) y := by
  rw [volumeFactor_basis_change]
  exact mul_pos targetFrameVolume_pos (Real.sqrt_pos.mpr
    (independentAmbientMetric_product_det_pos A rho hA hp hr hrp hrad p hy))

lemma independentAmbientMetric_target_det_pos (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    0 < (metricMatrix (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) y).det :=
  Real.sqrt_pos.mp (independentAmbientMetric_target_volume_pos A rho hA hp hr hrp hrad p hy)

end
end Yau.Target

end OAI
