import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicFlow

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesic_mulState (p : TangentBundle (model n) M) (a : ℝ) :
    geodesic (mulState a p) = fun t => geodesic p (a*t) :=
  completeGeodesic_unique (geodesic_complete _) (completeGeodesic_comp_mul (geodesic_complete p) a)

 theorem geodesicFlow_mulState (p : TangentBundle (model n) M) (a t : ℝ) :
    geodesicFlow t (mulState a p) = mulState a (geodesicFlow (a*t) p) := by
  change curveState (E := Model n) (geodesic (mulState a p)) t = _
  rw [geodesic_mulState]
  simpa only [add_zero,geodesicFlow] using curveState_comp_affine (E := Model n)
    (γ := geodesic p) (a := a) (b := 0) (t := t)
    ((geodesic_smooth p).mdifferentiable (by simp) _)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
