import OAI.Geometry.RCD.Heat.GaussianSubinterval
import OAI.Geometry.RCD.Heat.EntropyPowerSemicontinuous
import OAI.Geometry.RCD.Heat.UnitIntervalGaussianComparison

namespace OAI

/-! # Exact entropy-power interpolation on the actual bounded transport plan

The pointwise CD* bound and the proved Gaussian midpoint estimate imply the
hyperbolic interpolation, with the flat case obtained by an actual limit.
No entropic curvature-dimension premise is assumed here.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem exact_entropy_power_interpolation (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (t : Time) :
    let d := -(K*(wassersteinSq a.left a.right).toReal/N)
    let A := Real.exp (-(boltzmannEntropy (hausdorff n X) a.left)/N)
    let B := Real.exp (-(boltzmannEntropy (hausdorff n X) a.right)/N)
    (if d=0 then (1-(t:ℝ))*A+(t:ℝ)*B else hyperbolicChord (Real.sqrt d) A B t) ≤
      Real.exp (-(boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)))/N) := by
  let μ := hausdorff n X
  let u := fun s : Time => Real.exp (-(boltzmannEntropy μ (π.map (fun γ => γ s)))/N)
  let d := -(K*(wassersteinSq a.left a.right).toReal/N)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hd : 0 ≤ d := neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hK ENNReal.toReal_nonneg) hN0.le)
  have he := optimalPlan_endpoints a.left a.right π hp
  have hs (s : Time) : ∀ᵐ x ∂π.map (fun γ => γ s), x ∈ closedBall a.center (3*a.radius) := by
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono fun γ hγ => hγ.2 s
  let : IsFiniteMeasure (μ.restrict (closedBall a.center (3*a.radius))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall a.center (3*a.radius)).measure_lt_top.ne
  have hu : UpperSemicontinuous u := bounded_entropy_power_upperSemicontinuous μ
    measurableSet_closedBall π ENNReal.ofReal_ne_top hc hs hN0
  have hm (s t : Time) : Real.exp (-d*((s:ℝ)-(t:ℝ))^2/8)*(u s+u t)/2 ≤
      u (timeSegment s t midpointTime) := by
    have hex : -d*((s:ℝ)-(t:ℝ))^2/8=
        K*|(s:ℝ)-(t:ℝ)|^2*(wassersteinSq a.left a.right).toReal/(8*N) := by
      rw [sq_abs]
      dsimp only [d]
      ring
    rw [hex]
    exact hX.gaussian_entropy_midpoint_subinterval hn hK hN a π hg hp hC hc s t
  have hh := unitInterval_gaussian_comparison u hd hu (fun s => (Real.exp_pos _).le) hm t
  simpa only [u,μ,he.1,he.2] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
