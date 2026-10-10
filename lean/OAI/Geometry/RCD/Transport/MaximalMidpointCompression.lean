import OAI.Geometry.RCD.Transport.MaximalScalarMidpoint

namespace OAI

/-! # Compression of any actual maximal midpoint -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.maximal_midpoint_compressed
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hm : RenyiMaximizingPlan (hausdorff n X) a.left a.right π midpointTime q) :
    π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n a.distance a.capacity • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (κ : Measure C(Time,X)) (hgκ : ∀ᵐ γ ∂κ, IsGeodesic γ)
      (hpκ : IsOptimalCoupling a.left a.right (κ.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂κ.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right κ hgκ hpκ a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 midpointTime)
  have hml := hm.local_of_global μ measurableSet_closedBall hq0 hq1 (hs π hg hp)
    (fun κ _ hgκ hpκ => hs κ hgκ hpκ)
  exact hX.renyi_midpoint_compressed_short K n hn a.left a.right a.capacity_finite
    a.left_bound a.right_bound (finiteSecondMoment_of_bounded _ a.center a.left_support)
    (finiteSecondMoment_of_bounded _ a.center a.right_support) a.center a.radius_nonneg
    a.left_support a.right_support a.distance a.distance_bound π hg hp hq0 hq1 hml

end RegularPointCoordinates

end

end OAI
