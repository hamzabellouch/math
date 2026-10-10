import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GeodesicFlow
import OAI.Geometry.WeakMTW.Coordinates.TangentCoordinates
import OAI.Geometry.WeakMTW.Coordinates.CoordinateIdentification

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

 theorem geodesic_coordinate_equation_zero (x : M) (p : TangentBundle (model n) M)
    (hp : p.1 ∈ (chartAt (Model n) x).source) :
    HasDerivAt (fun t => (stateChart (E := Model n) x) (geodesicFlow t p))
      (geodesicSpray (metric x) (stateChart (E := Model n) x p)) 0 := by
  let c := chartAt (Model n) x
  let d := stateChart (E := Model n) x
  let q₀ := d p
  have hps : p ∈ d.source := (stateChart_source x p).mpr hp
  have hq₀ : q₀.1 ∈ c.target := (stateChart_target x q₀).mp (d.map_source hps)
  let A := metric x q₀.1 q₀.2 q₀.2
  obtain ⟨ε,hε,V,_hV,hmem,_hVS,hex⟩ := uniform_local_geodesics c.open_target
    (metric_smooth x) (fun y hy v hv => metric_positive x hy hv) hq₀ (1+|A|)
  have hbound : metric x q₀.1 q₀.2 q₀.2 ≤ (1+|A|)^2 := by
    dsimp only [A] at *
    nlinarith [le_abs_self (metric x q₀.1 q₀.2 q₀.2),sq_nonneg |metric x q₀.1 q₀.2 q₀.2|]
  obtain ⟨q,hqzero,hqs,hqe⟩ := hex q₀.1 hmem q₀.2 hbound
  have h0 : (0 : ℝ) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have he := geodesic_eq_coordinate x Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected
    hqs hqe h0
  rw [hqzero] at he
  change EqOn (geodesic (d.symm (d p))) _ _ at he
  rw [d.left_inv hps] at he
  have hstate : ∀ t ∈ Metric.ball (0 : ℝ) ε, d (geodesicFlow t p) = q t := by
    intro t ht
    have hh : geodesicFlow t p = d.symm (q t) := by
      change curveState (E := Model n) (geodesic p) t = _
      rw [← coordinate_curve_state_chart x (hqe t ht).1 (hqe t ht).2]
      apply curveState_congr
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      exact he hs
    rw [hh,d.right_inv ((stateChart_target x _).mpr (hqe t ht).1)]
  have hd := (hqe 0 h0).2
  rw [hqzero] at hd
  exact hd.congr_of_eventuallyEq (by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact hstate t ht)

 theorem geodesic_coordinate_equation (x : M) (p : TangentBundle (model n) M) (t : ℝ)
    (hp : geodesic p t ∈ (chartAt (Model n) x).source) :
    HasDerivAt (fun s => (stateChart (E := Model n) x) (geodesicFlow s p))
      (geodesicSpray (metric x) (stateChart (E := Model n) x (geodesicFlow t p))) t := by
  have hh := geodesic_coordinate_equation_zero x (geodesicFlow t p) hp
  have hd : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have he := hh.scomp_of_eq t hd (by simp)
  simpa only [Function.comp_def,one_smul,geodesicFlow_sub] using he
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
