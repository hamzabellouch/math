import OAI.Geometry.RCD.Metric.EuclideanAbsoluteContinuousBalls

namespace OAI

/-! # Comparing Lebesgue densities by midpoint contraction -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem local_midpoint_density_le {n : ℕ} (hn : 0 < n)
    (μ : FiniteMeasure (Euclidean n)) (hμ : (μ : Measure (Euclidean n)) ≪ volume)
    (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*(μ : Measure (Euclidean n)).real (ball v r) ≤
        (μ : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (u+v)) (r/2)))
    {x y : Euclidean n} (hx : x ∈ ball z (δ/4)) (hy : y ∈ ball z (δ/4))
    {a b : ℝ}
    (hlimx : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall x r)/
      volume.real (closedBall x r)) (𝓝[>] 0) (𝓝 a))
    (hlimy : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall y r)/
      volume.real (closedBall y r)) (𝓝[>] 0) (𝓝 b)) : a ≤ b := by
  let u := y+(y-x)
  have huy : dist u y = dist y x := by simp [u,dist_eq_norm]
  have hu : u ∈ ball z δ := by
    have h1 := dist_triangle u y z
    have h2 := dist_triangle y z x
    rw [huy] at h1
    rw [dist_comm z x] at h2
    have hx' : dist x z < δ/4 := hx
    have hy' : dist y z < δ/4 := hy
    change dist u z < δ
    linarith
  have hxδ : x ∈ ball z δ := (ball_subset_ball (by linarith)) hx
  have hmid : (1/2:ℝ) • (u+x)=y := by dsimp only [u]; module
  have hhalf : Tendsto (fun r : ℝ => r/2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa only [zero_div] using hh.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r/2
      exact div_pos (show 0 < r from hr) (by norm_num)
  have hlimy' := hlimy.comp hhalf
  apply le_of_tendsto_of_tendsto hlimx hlimy'
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hm := hc u hu x hxδ r hr.1 hr.2.le
  rw [hmid] at hm
  have he : (μ : Measure (Euclidean n)).real (closedBall x r) =
      (μ : Measure (Euclidean n)).real (ball x r) :=
    congrArg ENNReal.toReal (absolutelyContinuous_closedBall_eq_ball hn _ hμ x r)
  rw [← he] at hm
  exact half_ball_density_le hn _ x y hr.1 hm

theorem local_midpoint_density_eq {n : ℕ} (hn : 0 < n)
    (μ : FiniteMeasure (Euclidean n)) (hμ : (μ : Measure (Euclidean n)) ≪ volume)
    (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*(μ : Measure (Euclidean n)).real (ball v r) ≤
        (μ : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (u+v)) (r/2)))
    {x y : Euclidean n} (hx : x ∈ ball z (δ/4)) (hy : y ∈ ball z (δ/4))
    {a b : ℝ}
    (hlimx : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall x r)/
      volume.real (closedBall x r)) (𝓝[>] 0) (𝓝 a))
    (hlimy : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall y r)/
      volume.real (closedBall y r)) (𝓝[>] 0) (𝓝 b)) : a = b :=
  le_antisymm (local_midpoint_density_le hn μ hμ z hδ hc hx hy hlimx hlimy)
    (local_midpoint_density_le hn μ hμ z hδ hc hy hx hlimy hlimx)

end RegularPointCoordinates

end

end OAI
