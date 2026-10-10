import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 def tangentCoordinateEquiv (x p : M) (hp : p ∈ (chartAt (Model n) x).source) :
    TangentSpace (model n) p ≃L[ℝ] Model n :=
  (trivializationAt (Model n) (TangentSpace (model n)) x).continuousLinearEquivAt ℝ p
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hp)

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem tangentCoordinateEquiv_apply (x p : M) (hp : p ∈ (chartAt (Model n) x).source)
    (v : TangentSpace (model n) p) :
    tangentCoordinateEquiv x p hp v = (stateChart x (⟨p,v⟩ : TangentBundle (model n) M)).2 := rfl

 theorem tangentCoordinateEquiv_center (x : M) (v : TangentSpace (model n) x) :
    tangentCoordinateEquiv x x (mem_chart_source (Model n) x) v = tangentChartLinear x v :=
  (tangentChartLinear_eq x v).symm

 theorem stateChart_bary (x p : M) (hp : p ∈ (chartAt (Model n) x).source)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) p) (θ : κ → ℝ) :
    (stateChart x (⟨p,∑ i, θ i • a i⟩ : TangentBundle (model n) M)).2 =
      ∑ i, θ i • (stateChart x (⟨p,a i⟩ : TangentBundle (model n) M)).2 := by
  change tangentCoordinateEquiv x p hp (∑ i,θ i•a i) = ∑ i,θ i•tangentCoordinateEquiv x p hp (a i)
  simp only [map_sum,map_smul]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
