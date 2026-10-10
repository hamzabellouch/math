import OAI.Geometry.RCD.Metric.PointedMetricInteriorLift

namespace OAI

/-! # Identifying distances through the actual metric and value approximations -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

theorem metric_limit_distance_identification {q : Y} {S T : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y) (w : ℕ → X → Z) (F : Y → Z)
    (hr : ∀ k, 0<r k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hTS : T<S) (hF : Continuous F)
    (hvalues : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤T*r k → dist (w k x) (F (V k x))≤η)
    (hmetric : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x y,
      dist x (p k)≤T*r k → dist y (p k)≤T*r k →
        |dist (w k x) (w k y)-dist x y/r k|≤η) :
    ∀ y z, dist y q<T → dist z q<T → dist (F y) (F z)=dist y z := by
  intro y z hy hz
  obtain ⟨x,hx,hVx⟩ := pointed_metric_interior_lift p r ε V hr hε0 hV hTS hy
  obtain ⟨x',hx',hVx'⟩ := pointed_metric_interior_lift p r ε V hr hε0 hV hTS hz
  have hvalue (t : ℕ → X) (z : Y) (ht : ∀ᶠ k in atTop, dist (t k) (p k)≤T*r k)
      (hz : Tendsto (fun k => V k (t k)) atTop (𝓝 z)) :
      Tendsto (fun k => w k (t k)) atTop (𝓝 (F z)) := by
    apply ((hF.tendsto z).comp hz).congr_dist
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [ht,hvalues (η/2) (half_pos hη)] with k hk he
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,dist_comm]
    exact (he (t k) hk).trans_lt (half_lt_self hη)
  have hw := hvalue x y hx hVx
  have hw' := hvalue x' z hx' hVx'
  have hphysical : Tendsto (fun k => dist (x k) (x' k)/r k) atTop (𝓝 (dist y z)) := by
    apply (hVx.dist hVx').congr_dist
    have hb : ∀ᶠ k in atTop,
        dist (dist (V k (x k)) (V k (x' k))) (dist (x k) (x' k)/r k)≤ε k := by
      filter_upwards [hx,hx'] with k hk hk'
      rw [Real.dist_eq]
      exact (hV k).2.1 (x k) (x' k)
        (hk.trans (mul_le_mul_of_nonneg_right hTS.le (hr k).le))
        (hk'.trans (mul_le_mul_of_nonneg_right hTS.le (hr k).le))
    exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hb hε0
  have hphysical' : Tendsto (fun k => dist (x k) (x' k)/r k) atTop (𝓝 (dist (F y) (F z))) := by
    apply (hw.dist hw').congr_dist
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hx,hx',hmetric (η/2) (half_pos hη)] with k hk hk' he
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,Real.dist_eq]
    exact (he (x k) (x' k) hk hk').trans_lt (half_lt_self hη)
  exact tendsto_nhds_unique hphysical' hphysical

end RegularPointCoordinates

end

end OAI
