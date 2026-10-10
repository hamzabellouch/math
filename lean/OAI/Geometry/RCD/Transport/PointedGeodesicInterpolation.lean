import OAI.Geometry.RCD.Metric.EuclideanSegmentError

namespace OAI

/-! # Images of short source geodesics approach Euclidean affine segments

This estimate applies to every geodesic in a bounded endpoint region; no
choice of optimal plan or pointwise regularity of the approximation map
is required.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_geodesic_interpolation {n : ℕ} {p : X} {r S ρ ε : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hε : 0≤ε) (hroom : 3*ρ≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤ρ*r) (h1 : dist (γ 1) p≤ρ*r) (t : Time) :
    dist (v (γ t)) ((1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1))≤
      Real.sqrt (2*(ε*(4*ρ+ε))) := by
  have hD : dist (γ 0) (γ 1)≤2*ρ*r := by
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hh
    linarith
  have htd0 : dist (γ t) (γ 0)=(t:ℝ)*dist (γ 0) (γ 1) := by
    have hh := hγ t 0
    change dist (γ t) (γ 0)=|(t:ℝ)-0| *dist (γ 0) (γ 1) at hh
    simpa only [sub_zero,abs_of_nonneg t.2.1] using hh
  have htd1 : dist (γ t) (γ 1)=(1-(t:ℝ))*dist (γ 0) (γ 1) := by
    have hh := hγ t 1
    change dist (γ t) (γ 1)=|(t:ℝ)-1| *dist (γ 0) (γ 1) at hh
    simpa only [abs_of_nonpos (sub_nonpos.mpr t.2.2),neg_sub] using hh
  have htD : dist (γ t) (γ 0)≤dist (γ 0) (γ 1) := by
    rw [htd0]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  have hpoints (s : Time) : dist (γ s) p≤S*r := by
    have hsd0 : dist (γ s) (γ 0)≤dist (γ 0) (γ 1) := by
      rw [hγ s 0]
      change |(s:ℝ)-0| *dist (γ 0) (γ 1)≤dist (γ 0) (γ 1)
      simp only [sub_zero,abs_of_nonneg s.2.1]
      exact mul_le_of_le_one_left dist_nonneg s.2.2
    have hs := (dist_triangle (γ s) (γ 0) p).trans (add_le_add (hsd0.trans hD) h0)
    have hh := mul_le_mul_of_nonneg_right hroom hr.le
    linarith
  have hd : dist (γ 0) (γ 1)/r≤2*ρ := (div_le_iff₀ hr).mpr hD
  have hd0 : dist (γ t) (γ 0)/r≤2*ρ := (div_le_div_of_nonneg_right htD hr.le).trans hd
  have hd1 : dist (γ t) (γ 1)/r≤2*ρ := by
    apply (div_le_div_of_nonneg_right _ hr.le).trans hd
    rw [htd1]
    exact mul_le_of_le_one_left dist_nonneg (by linarith [t.2.1])
  have he0 := pointed_square_distance_error hr hε hv (hpoints t) (hpoints 0) hd0
  have he1 := pointed_square_distance_error hr hε hv (hpoints t) (hpoints 1) hd1
  have he01 := pointed_square_distance_error hr hε hv (hpoints 0) (hpoints 1) hd
  have he0' : dist (γ t) (γ 0)/r=(t:ℝ)*(dist (γ 0) (γ 1)/r) := by rw [htd0]; ring
  have he1' : dist (γ t) (γ 1)/r=(1-(t:ℝ))*(dist (γ 0) (γ 1)/r) := by rw [htd1]; ring
  rw [he0'] at he0
  rw [he1'] at he1
  have hE : 0≤ε*(2*(2*ρ)+ε) := mul_nonneg hε (by positivity)
  have heq : 2*(2*ρ)=4*ρ := by ring
  simpa only [heq] using euclidean_segment_error (v (γ 0)) (v (γ 1)) (v (γ t))
    t.2.1 t.2.2 hE he0 he1 he01

end RegularPointCoordinates

end

end OAI
