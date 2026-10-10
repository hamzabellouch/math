import OAI.Geometry.RCD.Metric.MetricLimitBallImage
import OAI.Geometry.RCD.Metric.PointedMetricInteriorLift

namespace OAI

/-! # Quantitative density transferred from a filled metric-limit ball -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem local_isometry_density_transfer {n : ℕ} {p : X} {q : Y} {r δ η τ : ℝ}
    (hr : 0<r) (hτ : 0<τ) (hδ : δ≤1/8192) (hδτ : δ≤τ/8192) (hητ : η≤τ/8192)
    (V : X → Y) (w : X → Euclidean n) (F : Y → Euclidean n)
    (hV : IsPointedApproximation p q r 5 δ V) (hFq : F q=0)
    (hiso : ∀ y z, dist y q<1/16 → dist z q<1/16 → dist (F y) (F z)=dist y z)
    (himage : F '' closedBall q (1/256)=closedBall 0 (1/256))
    (hvalues : ∀ x, dist x p≤5*r → dist (w x) (F (V x))≤η) :
    ∀ y : Euclidean n, dist y 0≤2-τ →
      ∃ x : X, dist x p≤2*(r/1024) ∧ dist ((1024:ℝ) • w x) y≤τ := by
  intro y hy
  let y' : Euclidean n := (1024:ℝ)⁻¹ • y
  have hyn : ‖y‖≤2-τ := by simpa only [dist_zero_right] using hy
  have hy'n : ‖y'‖=‖y‖/1024 := by
    dsimp [y']
    rw [norm_smul]
    norm_num [div_eq_mul_inv,mul_comm]
  have hy' : y'∈closedBall (0 : Euclidean n) (1/256) := by
    rw [mem_closedBall,dist_zero_right,hy'n]
    linarith
  rw [← himage] at hy'
  obtain ⟨z,hz,hFz⟩ := hy'
  have hz16 : dist z q<1/16 := (show dist z q≤1/256 from hz).trans_lt (by norm_num)
  have hzdist : dist z q=‖y‖/1024 := by
    rw [← hiso z q hz16 (by simp),hFz,hFq,dist_zero_right,hy'n]
  have hz5 : dist z q≤5-δ := by rw [hzdist]; linarith
  obtain ⟨x,hx5,hxz⟩ := hV.2.2 z hz5
  have hp5 : dist p p≤5*r := by simp; positivity
  have hxpd := (abs_le.mp (hV.2.1 x p hx5 hp5)).1
  have ht := dist_triangle4 (V x) z q (V p)
  rw [dist_comm q (V p)] at ht
  have hxrad : dist x p/r≤2/1024 := by
    rw [hzdist] at ht
    linarith [hV.1]
  have hx : dist x p≤2*(r/1024) := by
    have hh := (div_le_iff₀ hr).mp hxrad
    linarith
  have hx16 : dist (V x) q<1/16 := by
    have hh := dist_triangle (V x) z q
    rw [hzdist] at hh
    linarith
  have hvalue : dist (w x) y'≤η+δ := by
    have hh := dist_triangle (w x) (F (V x)) (F z)
    rw [hiso (V x) z hx16 hz16,hFz] at hh
    linarith [hvalues x hx5]
  refine ⟨x,hx,?_⟩
  have he : (1024:ℝ) • y'=y := by simp [y',smul_smul]
  rw [← he,dist_smul₀]
  norm_num
  linarith

end RegularPointCoordinates

end

end OAI
