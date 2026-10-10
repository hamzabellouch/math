import OAI.Geometry.RCD.Transport.PointedGeodesicWithin

namespace OAI

/-! # Metric preimages of balls interpolate inside the expected midpoint ball -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_midpoint_balls_within {n : ℕ} {p : X} {r S ρ ε a b : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hε : 0≤ε)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    {x y : Euclidean n} {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤ρ*r) (h1 : dist (γ 1) p≤ρ*r)
    (hpoints : ∀ t : Time, dist (γ t) p≤S*r)
    (hx : dist (V (γ 0)) x≤a) (hy : dist (V (γ 1)) y≤b) :
    V (γ midpointTime) ∈ closedBall ((1/2:ℝ) • (x+y))
      ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) := by
  have ht := pointed_geodesic_interpolation_within hr hρ hε hV hγ h0 h1 hpoints midpointTime
  have hdist : dist ((1/2:ℝ) • V (γ 0)+(1/2:ℝ) • V (γ 1))
      ((1/2:ℝ) • (x+y)) ≤ (a+b)/2 := by
    rw [smul_add]
    have hh := dist_add_add_le ((1/2:ℝ) • V (γ 0)) ((1/2:ℝ) • V (γ 1))
      ((1/2:ℝ) • x) ((1/2:ℝ) • y)
    simp only [dist_smul₀,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hh
    linarith
  change dist (V (γ midpointTime)) ((1/2:ℝ) • (x+y))≤_
  norm_num only [midpointTime,show (1-(1/2:ℝ))=1/2 by norm_num] at ht
  exact (dist_triangle (V (γ midpointTime))
    ((1/2:ℝ) • V (γ 0)+(1/2:ℝ) • V (γ 1)) ((1/2:ℝ) • (x+y))).trans
      (by linarith)

theorem pointed_midpoint_balls {n : ℕ} {p : X} {r S ρ ε a b : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hε : 0≤ε) (hroom : 3*ρ≤S)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    {x y : Euclidean n} {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p≤ρ*r) (h1 : dist (γ 1) p≤ρ*r)
    (hx : dist (V (γ 0)) x≤a) (hy : dist (V (γ 1)) y≤b) :
    V (γ midpointTime) ∈ closedBall ((1/2:ℝ) • (x+y))
      ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) := by
  apply pointed_midpoint_balls_within hr hρ hε hV hγ h0 h1 _ hx hy
  intro t
  have hd := dist_triangle (γ 0) p (γ 1)
  rw [dist_comm p (γ 1)] at hd
  have ht : dist (γ t) (γ 0) ≤ dist (γ 0) (γ 1) := by
    rw [hγ t 0]
    change |(t:ℝ)-0| * dist (γ 0) (γ 1) ≤ dist (γ 0) (γ 1)
    simp only [sub_zero,abs_of_nonneg t.2.1]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  have hb := dist_triangle (γ t) (γ 0) p
  nlinarith [mul_le_mul_of_nonneg_right hroom hr.le]

end RegularPointCoordinates

end

end OAI
