import OAI.Geometry.RCD.Transport.RadialGeodesic

namespace OAI

/-! # Uniqueness forced by the quadratic distance identities

The identity is tested at a point on a competing geodesic. Its right hand
side then vanishes, so no nonbranching assumption is needed.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem quadratic_geodesic_unique (γ η : C(Time,X)) (hη : IsGeodesic η)
    (h0 : η 0=γ 0) (h1 : η 1=γ 1)
    (he : ∀ z : X, ∀ t : Time, dist z (γ t)^2 =
      (1-(t:ℝ))*dist z (γ 0)^2+(t:ℝ)*dist z (γ 1)^2-
        (t:ℝ)*(1-(t:ℝ))*dist (γ 0) (γ 1)^2) : η=γ := by
  ext t
  have hx : dist (η t) (γ 0)=(t:ℝ)*dist (γ 0) (γ 1) := by
    have hh := hη t 0
    rw [h0,h1] at hh
    change dist (η t) (γ 0)=|(t:ℝ)-0| *dist (γ 0) (γ 1) at hh
    simpa only [sub_zero,abs_of_nonneg t.property.1] using hh
  have hy : dist (η t) (γ 1)=(1-(t:ℝ))*dist (γ 0) (γ 1) := by
    have hh := hη t 1
    rw [h0,h1] at hh
    change dist (η t) (γ 1)=|(t:ℝ)-1| *dist (γ 0) (γ 1) at hh
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr t.property.2)] at hh
    exact hh
  have hz : dist (η t) (γ t)^2=0 := by
    rw [he (η t) t,hx,hy]
    ring
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem quadratic_radial_distance
    (γ η : C(Time,X)) (hη : IsGeodesic η) (h0 : γ 0=η 0)
    (hγe : ∀ z : X, ∀ t : Time, dist z (γ t)^2 =
      (1-(t:ℝ))*dist z (γ 0)^2+(t:ℝ)*dist z (γ 1)^2-
        (t:ℝ)*(1-(t:ℝ))*dist (γ 0) (γ 1)^2)
    (hηe : ∀ z : X, ∀ t : Time, dist z (η t)^2 =
      (1-(t:ℝ))*dist z (η 0)^2+(t:ℝ)*dist z (η 1)^2-
        (t:ℝ)*(1-(t:ℝ))*dist (η 0) (η 1)^2) (t : Time) :
    dist (γ t) (η t)=(t:ℝ)*dist (γ 1) (η 1) := by
  have hr : dist (η t) (γ 0)=(t:ℝ)*dist (η 0) (η 1) := by
    rw [h0,hη t 0]
    change |(t:ℝ)-0| *dist (η 0) (η 1)=(t:ℝ)*dist (η 0) (η 1)
    simp only [sub_zero,abs_of_nonneg t.property.1]
  have hm := hηe (γ 1) t
  rw [← h0] at hm
  rw [dist_comm (γ 1) (γ 0)] at hm
  have he := hγe (η t) t
  rw [hr,dist_comm (η t) (γ 1),hm,← h0] at he
  have hs : dist (γ t) (η t)^2=((t:ℝ)*dist (γ 1) (η 1))^2 := by
    rw [dist_comm]
    nlinarith only [he]
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg t.property.1 dist_nonneg)).mp hs

end RegularPointCoordinates

end

end OAI
