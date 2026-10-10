import OAI.Geometry.RCD.Metric.ScaledImageHoleVolume
import OAI.Geometry.RCD.Coordinates.CenteredCoordinateNorm

namespace OAI

/-! # The image-hole estimate for the actual coarse and fine coordinate data -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.coarse_fine_image_hole_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {R ρ η : ℝ} {C : ℝ≥0}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : 64*ρ ≤ R) (hC : 1 ≤ (C:ℝ))
    (hcurv : -1 ≤ K*(32*R)^2) (hη : (2*R)*(η/4) ≤ ρ/4)
    {v : X → Euclidean n} {U : Set X} (hU : IsCompact U) (hUsub : U ⊆ closedBall p R)
    (hglobal : LipschitzOnWith C v (ball p (4*R)))
    (hcoarse : IsPointedApproximation p 0 (2*R) (1/2) (η/4)
      (fun x => (2*R)⁻¹ • (v x-v p)))
    (hfine : ∀ z ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation z 0 r (1/16) (1/128) (fun x => r⁻¹ • (v x-v z)))
    (hpoint : ∃ z ∈ U, dist z p < ρ/4) :
    volume.real (ball (0 : Euclidean n) ρ \ (fun x => v x-v p) '' U) ≤
      (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
        (((4*(C:ℝ))^n*(Real.cosh 1^(n-1)*2^n)*(16*R)^n/
          (hausdorff n X).real (ball p (16*R)))*
          (hausdorff n X).real (ball p R \ U)) := by
  let u := fun x => v x-v p
  have hρR' : ρ ≤ R := by linarith only [hρR,hρ]
  have hUball : U ⊆ ball p (4*R) := by
    intro z hz
    exact mem_ball.mpr ((hUsub hz).trans_lt (by linarith only [hR]))
  have hucont : ContinuousOn u U := (hglobal.continuousOn.mono hUball).sub continuousOn_const
  have hnear (z : X) (hz : z ∈ U) (hi : u z ∈ ball 0 ρ) : dist z p < 2*ρ := by
    have hloc := centered_coordinate_preimage_ball (by positivity : 0 < 2*R)
      (by norm_num : (0:ℝ)≤1/2) hη hcoarse
      (show dist z p ≤ (1/2)*(2*R) by have hh := hUsub hz; change dist z p ≤ R at hh; linarith) hi
    change dist z p < ρ+ρ/4 at hloc
    linarith only [hloc,hρ]
  apply hX.image_hole_volume_at_radius_le hn hρ (by linarith only [hR,hρR']) hC
    (by convert hcurv using 1; ring) (hU.image_of_continuousOn hucont).isClosed
  · obtain ⟨z,hz,hzp⟩ := hpoint
    refine ⟨u z,?_,⟨z,hz,rfl⟩⟩
    have hb := (centered_coordinate_norm_bounds (by positivity : 0 < 2*R)
      (by norm_num : (0:ℝ)≤1/2) hcoarse
      (show dist z p ≤ (1/2)*(2*R) by have hh := hUsub hz; change dist z p ≤ R at hh; linarith)).2
    rw [mem_ball,dist_zero_right]
    change ‖v z-v p‖ < ρ
    linarith only [hb,hzp,hη,hρ]
  · exact measure_ne_top_of_subset sdiff_subset (hX.finiteOnBounded _ isBounded_ball).ne
  · intro z hz hi
    linarith only [hnear z hz hi,hρR,hρ]
  · intro z hz r hr hrρ
    have hh := hfine z hz (64*r) (by positivity) (by linarith only [hrρ,hρR])
    simpa only [u,sub_sub_sub_cancel_right] using hh
  · intro z hz hi x hx y hy
    have hxy : dist y x < ρ/(4*(C:ℝ)) := hy
    have hsmall : ρ/(4*(C:ℝ)) ≤ ρ := div_le_self hρ.le (by linarith only [hC])
    have ht := (dist_triangle y x z).trans (add_le_add hxy.le hx)
    have hp := (dist_triangle y z p).trans (add_le_add ht (hnear z hz hi).le)
    exact mem_ball.mpr (by linarith only [hp,hsmall,hρR,hρ,hxy])
  · intro x hx y hy
    simpa only [u,dist_sub_right] using hglobal.dist_le_mul x
      (ball_subset_ball (by linarith only [hR]) hx) y
      (ball_subset_ball (by linarith only [hR]) hy)

end RegularPointCoordinates

end

end OAI
