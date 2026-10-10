import OAI.Geometry.RCD.Transport.PointedGeodesicWithin
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Geodesic control from nearby image endpoints anywhere in the interior -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_local_geodesic_within {n : ℕ} {p : X} {r S τ η ε : ℝ}
    (hr : 0<r) (hτS : τ≤S) (hroom : τ+2*η+ε≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤τ*r) (h1 : dist (γ 1) p≤τ*r)
    (z : Euclidean n) (hz0 : v (γ 0)∈closedBall z η) (hz1 : v (γ 1)∈closedBall z η) :
    ∀ t : Time, dist (γ t) p≤S*r := by
  have hsr := mul_le_mul_of_nonneg_right hτS hr.le
  have he := (abs_le.mp (hv.2.1 _ _ (h0.trans hsr) (h1.trans hsr))).1
  have him : dist (v (γ 0)) (v (γ 1))≤2*η := by
    have ht := dist_triangle (v (γ 0)) z (v (γ 1))
    rw [dist_comm z (v (γ 1))] at ht
    change dist (v (γ 0)) z≤η at hz0
    change dist (v (γ 1)) z≤η at hz1
    linarith
  have hD : dist (γ 0) (γ 1)≤(2*η+ε)*r := (div_le_iff₀ hr).mp (by linarith)
  intro t
  have ht : dist (γ t) (γ 0)≤dist (γ 0) (γ 1) := by
    rw [hγ t 0]
    change |(t:ℝ)-0| *dist (γ 0) (γ 1)≤dist (γ 0) (γ 1)
    simp only [sub_zero,abs_of_nonneg t.2.1]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  have hb := (dist_triangle (γ t) (γ 0) p).trans (add_le_add (ht.trans hD) h0)
  nlinarith [mul_le_mul_of_nonneg_right hroom hr.le]

theorem pointed_local_geodesic_image {n : ℕ} {p : X} {r S τ η ε : ℝ}
    (hr : 0<r) (hτ : 0≤τ) (hτS : τ≤S) (hε : 0≤ε) (hroom : τ+2*η+ε≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤τ*r) (h1 : dist (γ 1) p≤τ*r)
    (z : Euclidean n) (hz0 : v (γ 0)∈closedBall z η) (hz1 : v (γ 1)∈closedBall z η)
    (t : Time) : dist (v (γ t)) z≤η+Real.sqrt (2*(ε*(4*τ+ε))) := by
  have hpoints := pointed_local_geodesic_within hr hτS hroom hv hγ h0 h1 z hz0 hz1
  have he := pointed_geodesic_interpolation_within hr hτ hε hv hγ h0 h1 hpoints t
  have hc : (1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1)∈closedBall z η :=
    (convex_closedBall z η) hz0 hz1 (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  exact (dist_triangle _ _ _).trans ((add_le_add he hc).trans_eq (add_comm _ _))

end RegularPointCoordinates

end

end OAI
