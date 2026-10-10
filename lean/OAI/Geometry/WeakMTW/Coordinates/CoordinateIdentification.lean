import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicFlow
import OAI.Geometry.WeakMTW.Coordinates.TangentCoordinates

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
  [IsRiemannianManifold (model n) M] [CompactSpace M]
 theorem geodesic_eq_coordinate (x : M) {U : Set ℝ} (hU : IsOpen U) (hpre : IsPreconnected U)
    {q : ℝ → Model n × Model n} (hqs : ContDiffOn ℝ ∞ q U)
    (hqe : ∀ t ∈ U, (q t).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t) (h0 : (0 : ℝ) ∈ U) :
    EqOn (geodesic ((stateChart (E := Model n) x).symm (q 0)))
      (fun t => (chartAt (Model n) x).symm (q t).1) U := by
  let p := (stateChart (E := Model n) x).symm (q 0)
  have hγ := coordinate_intrinsic x hU hpre hqs hqe h0
  have hn : Real.sqrt (metric x (q 0).1 (q 0).2 (q 0).2) = ‖p.2‖ :=
    stateChart_energy x (q := q 0) (hqe 0 h0).1
  rw [hn] at hγ
  have hγ₀ := coordinate_curve_state_chart x (hqe 0 h0).1 (hqe 0 h0).2
  exact intrinsic_unique_on hU hpre (norm_nonneg p.2) (norm_nonneg p.2)
    ((geodesic_intrinsic p).mono (subset_univ U)) hγ h0
    ((geodesic_state_zero p).trans hγ₀.symm)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
