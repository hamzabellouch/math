import OAI.Geometry.RCD.Metric.ComponentDistanceNodes
import OAI.Geometry.RCD.Transport.GlobalRenyiLeftComponent
import OAI.Geometry.RCD.Transport.GlobalRenyiRightComponent
import OAI.Geometry.RCD.Coordinates.RenyiScalarNormalization

namespace OAI

/-! # Scalar reduced midpoint bounds for actual length components

The component length bound, rather than the parent diameter, appears in
both half estimates. Normalization cancels exactly. Midpoint maximality is
inherited from the parent and is not postulated for the component.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.component_scalar_midpoints
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {D : ℝ} (hD0 : 0≤D)
    (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D)
    (hmaxL : RenyiMaximizingPlan (hausdorff n X)
      (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (π.map (subpath 0 midpointTime)) midpointTime (1-1/N))
    (hmaxR : RenyiMaximizingPlan (hausdorff n X)
      (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))
      (π.map (subpath midpointTime 1)) midpointTime (1-1/N)) :
    (sigma K (N+1) (1/2) (D/2) *
      (renyiIntegral (hausdorff n X) (κ.map (fun γ => γ 0)) N+
       renyiIntegral (hausdorff n X) (κ.map (fun γ => γ midpointTime)) N) ≤
      renyiIntegral (hausdorff n X) (κ.map (fun γ => γ (lowerTime midpointTime))) N) ∧
    (sigma K (N+1) (1/2) (D/2) *
      (renyiIntegral (hausdorff n X) (κ.map (fun γ => γ midpointTime)) N+
       renyiIntegral (hausdorff n X) (κ.map (fun γ => γ 1)) N) ≤
      renyiIntegral (hausdorff n X) (κ.map (fun γ => γ (upperTime midpointTime))) N) := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N<1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hc : κ univ≠∞ := measure_ne_top κ univ
  obtain ⟨b₀,b₁,h0,hm0,hm1,h1,hd0,hd1⟩ := hX.exists_length_bounded_half_nodes
    K n hn a π hg hp hC hcomp κ hκ hκ0 hD0 hD
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,hfn⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  obtain ⟨hL,hgL,hpL⟩ := geodesic_subpath_law πn hgn hpn hfn 0 midpointTime
  obtain ⟨hR,hgR,hpR⟩ := geodesic_subpath_law πn hgn hpn hfn midpointTime 1
  let := hL
  let := hR
  have hmapL : πn.map (subpath 0 midpointTime)=(κ univ)⁻¹ • κ.map (subpath 0 midpointTime) :=
    Measure.map_smul _ (subpath_measurable 0 midpointTime).aemeasurable
  have hmapR : πn.map (subpath midpointTime 1)=(κ univ)⁻¹ • κ.map (subpath midpointTime 1) :=
    Measure.map_smul _ (subpath_measurable midpointTime 1).aemeasurable
  have hmL : RenyiMaximizingPlan μ b₀.left b₀.right (πn.map (subpath 0 midpointTime))
      midpointTime (1-1/N) := by
    rw [h0,hm0,hmapL]
    exact hX.global_renyi_left_component K n hn a π hg hp hS κ hκeq hκ0 hq0 hq1 hmaxL
  have hmR : RenyiMaximizingPlan μ b₁.left b₁.right (πn.map (subpath midpointTime 1))
      midpointTime (1-1/N) := by
    rw [hm1,h1,hmapR]
    exact hX.global_renyi_right_component K n hn a π hg hp hS κ hκeq hκ0 hq0 hq1 hmaxR
  have hpL' : IsOptimalCoupling b₀.left b₀.right
      ((πn.map (subpath 0 midpointTime)).map (fun γ => (γ 0,γ 1))) := by
    rw [h0,hm0,←heval,←heval]; exact hpL
  have hpR' : IsOptimalCoupling b₁.left b₁.right
      ((πn.map (subpath midpointTime 1)).map (fun γ => (γ 0,γ 1))) := by
    rw [hm1,h1,←heval,←heval]; exact hpR
  have hbL := hX.maximal_scalar_midpoint K n hn hK hN b₀ _ hgL hpL' hmL
  have hbR := hX.maximal_scalar_midpoint K n hn hK hN b₁ _ hgR hpR' hmR
  rw [h0,hm0,hd0,subpath_map_eval πn 0 midpointTime midpointTime,heval] at hbL
  rw [hm1,h1,hd1,subpath_map_eval πn midpointTime 1 midpointTime,heval] at hbR
  exact ⟨renyiIntegral_normalized_bound μ _ _ _ hκ0 hc hN1 hbL,
    renyiIntegral_normalized_bound μ _ _ _ hκ0 hc hN1 hbR⟩

end RegularPointCoordinates

end

end OAI
