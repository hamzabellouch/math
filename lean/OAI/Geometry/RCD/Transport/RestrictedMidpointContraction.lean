import OAI.Geometry.RCD.Metric.MetricLimitLocalContraction

namespace OAI

/-! # Restricting the local contraction to an interior Euclidean ball -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem restrict_midpoint_contraction {n : ℕ}
    (μ : Measure (Euclidean n)) (z : Euclidean n) {S δ : ℝ} (hδ : 0 < δ)
    (hroom : ‖z‖+2*δ < S)
    (hc : ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*μ.real (ball v r) ≤ μ.real (closedBall ((1/2:ℝ) • (u+v)) (r/2))) :
    ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*(μ.restrict (ball 0 S)).real (ball v r) ≤
        (μ.restrict (ball 0 S)).real (closedBall ((1/2:ℝ) • (u+v)) (r/2)) := by
  intro u hu v hv r hr hrδ
  have houter : ball z (2*δ) ⊆ ball (0 : Euclidean n) S := by
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]
    linarith
  have hsource : ball v r ⊆ ball (0 : Euclidean n) S := by
    apply Subset.trans _ houter
    intro x hx
    have hh := dist_triangle x v z
    have hx' : dist x v < r := hx
    have hv' : dist v z < δ := hv
    change dist x z < 2*δ
    linarith
  have hmid : (1/2:ℝ) • (u+v) ∈ ball z δ := by
    rw [smul_add]
    exact (convex_ball z δ) hu hv (by norm_num) (by norm_num) (by norm_num)
  have htarget : closedBall ((1/2:ℝ) • (u+v)) (r/2) ⊆ ball (0 : Euclidean n) S := by
    apply Subset.trans _ houter
    intro x hx
    have hh := dist_triangle x ((1/2:ℝ) • (u+v)) z
    have hx' : dist x ((1/2:ℝ) • (u+v)) ≤ r/2 := hx
    have hm' : dist ((1/2:ℝ) • (u+v)) z < δ := hmid
    change dist x z < 2*δ
    linarith
  have he (A : Set (Euclidean n)) (hA : MeasurableSet A) (hsub : A ⊆ ball 0 S) :
      (μ.restrict (ball 0 S)).real A=μ.real A := by
    rw [Measure.real,Measure.real,Measure.restrict_apply hA,inter_eq_left.mpr hsub]
  rw [he _ measurableSet_ball hsource,he _ measurableSet_closedBall htarget]
  exact hc u hu v hv r hr hrδ

end RegularPointCoordinates

end

end OAI
