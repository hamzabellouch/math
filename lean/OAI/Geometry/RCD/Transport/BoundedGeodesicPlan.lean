import OAI.Analysis.RCDHeat.CompressionIntegral

namespace OAI

/-! # A common bounded region for a plan with bounded endpoints -/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem geodesic_plan_ball_support (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (p : X) {R : ℝ}
    (h0 : ∀ᵐ γ ∂π, dist p (γ 0) ≤ R) (h1 : ∀ᵐ γ ∂π, dist p (γ 1) ≤ R) :
    ∀ᵐ γ ∂π, ∀ s : Time, γ s ∈ closedBall p (3*R) := by
  filter_upwards [hgeo,h0,h1] with γ hγ h0 h1
  intro s
  have hlength : dist (γ 0) (γ 1) ≤ 2*R := by
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm (γ 0) p] at hh
    linarith
  have hdist : dist (γ s) (γ 0) = (s:ℝ)*dist (γ 0) (γ 1) := by
    simpa [abs_of_nonneg s.property.1] using hγ s 0
  rw [mem_closedBall,dist_comm]
  have hh := dist_triangle p (γ 0) (γ s)
  rw [dist_comm (γ 0) (γ s),hdist] at hh
  have hmul := mul_le_mul_of_nonneg_right s.property.2 (dist_nonneg (x := γ 0) (y := γ 1))
  linarith

theorem geodesic_plan_eval_ball (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (p : X) {R : ℝ}
    (h0 : ∀ᵐ γ ∂π, dist p (γ 0) ≤ R) (h1 : ∀ᵐ γ ∂π, dist p (γ 1) ≤ R)
    (s : Time) : ∀ᵐ x ∂π.map (fun γ => γ s), x ∈ closedBall p (3*R) := by
  apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
  exact (geodesic_plan_ball_support π hgeo p h0 h1).mono fun γ hγ => hγ s

end RegularPointCoordinates

end OAI
