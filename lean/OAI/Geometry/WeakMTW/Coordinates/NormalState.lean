import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicFlow
import OAI.Geometry.WeakMTW.Coordinates.NormalEndpoint

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesicFlow_eq_coordinate (x : M) {U : Set ℝ} (hU : IsOpen U) (hpre : IsPreconnected U)
    {q : ℝ → Model n × Model n} (hqs : ContDiffOn ℝ ∞ q U)
    (hqe : ∀ t ∈ U, (q t).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t) (h0 : (0 : ℝ) ∈ U)
    {t : ℝ} (ht : t ∈ U) :
    geodesicFlow t ((stateChart (E := Model n) x).symm (q 0)) =
      (stateChart x).symm (q t) := by
  have he := geodesic_eq_coordinate x hU hpre hqs hqe h0
  have he' : geodesic ((stateChart (E := Model n) x).symm (q 0)) =ᶠ[𝓝 t]
      (fun r => (chartAt (Model n) x).symm (q r).1) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds ht,he⟩
  rw [← coordinate_curve_state_chart x (hqe t ht).1 (hqe t ht).2]
  exact curveState_congr he'

 theorem geodesicFlow_normal (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ N.normal.source) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) N.time) :
    geodesicFlow t ((stateChart (E := Model n) x).symm q) =
      (stateChart x).symm (N.flow (t,q)) := by
  let S : Set ℝ := {t | (t,q) ∈ N.domain}
  have hS : IsOpen S := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨a,b,ha,hb,hJ⟩ := open_interval_around_segment hS N.time_pos.le (N.source_stays q hq)
  have h0J : (0 : ℝ) ∈ Ioo a b := ⟨ha,lt_trans N.time_pos hb⟩
  have htJ : t ∈ Ioo a b := ⟨lt_of_lt_of_le ha ht.1,lt_of_le_of_lt ht.2 hb⟩
  have hqs : ContDiffOn ℝ ∞ (fun r => N.flow (r,q)) (Ioo a b) :=
    N.flow_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) hJ
  have hqe := fun r hr => N.ode (r,q) (hJ hr)
  have hh := geodesicFlow_eq_coordinate x isOpen_Ioo (convex_Ioo a b).isPreconnected hqs hqe h0J htJ
  simpa only [N.initial q (hJ h0J)] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
