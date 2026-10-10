import OAI.Geometry.RCD.Heat.ExactEntropyPower
import OAI.Geometry.RCD.Coordinates.RegularizedEntropyFirstVariation
import OAI.Geometry.RCD.Heat.EntropyPowerBarrier

namespace OAI

/-! # Finite-dimensional first variation on the actual compressed RCD plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem entropic_plan_first_variation (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (r : Lp ℝ 2 (hausdorff n X)) {h : X → ℝ}
    (hr : (r : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[hausdorff n X] fun x => (a.left.rnDeriv (hausdorff n X) x).toReal)
    {d : ℝ} (hd : Tendsto (regularizedPlanLogSecant π h) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    d ≤ entropyPowerRate N (-(K*(wassersteinSq a.left a.right).toReal/N))
      (Real.exp (-boltzmannEntropy (hausdorff n X) a.left/N))
      (Real.exp (-boltzmannEntropy (hausdorff n X) a.right/N)) := by
  let μ := hausdorff n X
  let c := -(K*(wassersteinSq a.left a.right).toReal/N)
  let A := Real.exp (-boltzmannEntropy μ a.left/N)
  let B := Real.exp (-boltzmannEntropy μ a.right/N)
  let := a.left_probability
  let := a.right_probability
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hc0 : 0 ≤ c := neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hK ENNReal.toReal_nonneg) hN0.le)
  have he := optimalPlan_endpoints a.left a.right π hp
  have hs (s : Time) : ∀ᵐ x ∂π.map (fun γ => γ s), x ∈ closedBall a.center (3*a.radius) := by
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono fun γ hγ => hγ.2 s
  let : IsFiniteMeasure (μ.restrict (closedBall a.center (3*a.radius))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall a.center (3*a.radius)).measure_lt_top.ne
  have het (s : Time) := entropy_integrable_of_bounded_support μ (π.map (fun γ => γ s))
    ENNReal.ofReal_ne_top (hc s) measurableSet_closedBall (hs s)
  have hA : 0 < A := Real.exp_pos _
  have hbar (s : Time) : entropyPowerChord c A B s ≤
      Real.exp (-boltzmannEntropy μ (π.map (fun γ => γ s))/N) :=
    hX.exact_entropy_power_interpolation hn hK hN a π hg hp hC hc s
  have hh := regularized_entropy_power_first_variation μ a.left r hr hrn
    (by simpa only [he.1] using het 0) π he.1 ENNReal.ofReal_ne_top hc measurableSet_closedBall hs het
    hN0 (entropyPowerChord_zero hc0 A B) (hasDerivAt_entropyPowerChord_zero c A B) hbar hd
  change d ≤ entropyPowerRate N c A B
  rw [entropyPowerRate_eq hc0 hA]
  simpa only [entropyPowerChord_zero hc0] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
