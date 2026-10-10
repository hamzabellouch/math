import OAI.Geometry.RCD.Transport.RenyiScalarMidpoint
import OAI.Geometry.RCD.Transport.LocalRenyiMaximality

namespace OAI

/-! # The scalar reduced estimate for any actual maximal midpoint

No selected-plan identity is required. The proved compression theorem
supplies the node's midpoint bound for the given variational maximizer.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.maximal_scalar_midpoint
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hm : RenyiMaximizingPlan (hausdorff n X) a.left a.right π midpointTime (1-1/N)) :
    sigma K (N+1) (1/2) a.distance *
      (renyiIntegral (hausdorff n X) a.left N+renyiIntegral (hausdorff n X) a.right N) ≤
      renyiIntegral (hausdorff n X) (π.map (fun γ => γ midpointTime)) N := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN1 : 1<N := by linarith
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N<1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  have hs (κ : Measure C(Time,X)) (hgκ : ∀ᵐ γ ∂κ, IsGeodesic γ)
      (hpκ : IsOptimalCoupling a.left a.right (κ.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂κ.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right κ hgκ hpκ a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 midpointTime)
  have hml := hm.local_of_global μ measurableSet_closedBall hq0 hq1 (hs π hg hp)
    (fun κ _ hgκ hpκ => hs κ hgκ hpκ)
  have hcap := hX.renyi_midpoint_compressed_short K n hn a.left a.right a.capacity_finite
    a.left_bound a.right_bound (finiteSecondMoment_of_bounded _ a.center a.left_support)
    (finiteSecondMoment_of_bounded _ a.center a.right_support) a.center a.radius_nonneg
    a.left_support a.right_support a.distance a.distance_bound π hg hp hq0 hq1 hml
  exact hX.renyiNode_scalar_midpoint K n hn hK hN a ⟨π,inferInstance,hg,hp,hcap,hm⟩

end RegularPointCoordinates

end

end OAI
