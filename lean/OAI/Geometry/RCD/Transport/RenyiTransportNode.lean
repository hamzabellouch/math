import OAI.Geometry.RCD.Transport.RenyiDyadicConstruction

namespace OAI

/-! # Fixed nodes for compatible Rényi refinement

A node records only the bounded transport data needed at that segment.
Its selected maximal midpoint is independent of any requested tree depth.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

structure RenyiTransportNode (n : ℕ) (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  left : Measure X
  right : Measure X
  left_probability : IsProbabilityMeasure left
  right_probability : IsProbabilityMeasure right
  center : X
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  left_support : ∀ᵐ x ∂left, dist x center ≤ radius
  right_support : ∀ᵐ x ∂right, dist x center ≤ radius
  capacity : ℝ≥0∞
  capacity_finite : capacity ≠ ∞
  left_bound : left ≤ capacity • hausdorff n X
  right_bound : right ≤ capacity • hausdorff n X
  distance : ℝ
  distance_nonneg : 0 ≤ distance
  distance_bound : OptimalPlanDistanceBound left right distance

structure RenyiNodeSplit {n : ℕ} (K q : ℝ) (a : RenyiTransportNode n X) where
  plan : Measure C(Time,X)
  probability : IsProbabilityMeasure plan
  geodesic : ∀ᵐ γ ∂plan, IsGeodesic γ
  optimal : IsOptimalCoupling a.left a.right (plan.map (fun γ => (γ 0,γ 1)))
  compressed : plan.map (fun γ => γ midpointTime) ≤
    midpointCapacity K n a.distance a.capacity • hausdorff n X
  maximal : RenyiMaximizingPlan (hausdorff n X) a.left a.right plan midpointTime q

theorem NoncollapsedRCD.renyiNodeSplit_nonempty
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (a : RenyiTransportNode n X) :
    Nonempty (RenyiNodeSplit K q a) := by
  let := a.left_probability
  let := a.right_probability
  obtain ⟨π,hπ,hg,hp,hc,hm⟩ := hX.exists_global_renyi_midpoint_short K n hn
    a.left a.right a.capacity_finite a.left_bound a.right_bound a.center a.radius_nonneg
    a.left_support a.right_support a.distance a.distance_bound hq0 hq1
  exact ⟨⟨π,hπ,hg,hp,hc,hm⟩⟩

noncomputable def NoncollapsedRCD.selectedRenyiSplit
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (a : RenyiTransportNode n X) : RenyiNodeSplit K q a :=
  Classical.choice (hX.renyiNodeSplit_nonempty K n hn q hq0 hq1 a)

end RegularPointCoordinates

end

end OAI
