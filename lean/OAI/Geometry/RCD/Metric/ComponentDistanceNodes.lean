import OAI.Geometry.RCD.Metric.ComponentHalfDistance
import OAI.Geometry.RCD.Coordinates.NormalizedSubplanNodes

namespace OAI

/-! # Transport nodes at the actual component length scale -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.component_half_distance_bounds
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    {D : ℝ} (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    OptimalPlanDistanceBound ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime)) (D/2) ∧
    OptimalPlanDistanceBound ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) (D/2) := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
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
  rw [heval,heval] at hpL hpR
  let := hL
  let := hR
  constructor
  · intro q hq hgq hpq
    let := hq
    exact (hX.component_splice_distance K n hn a π hg hp κ hκ hκ0 hD
      q (πn.map (subpath midpointTime 1)) hgq hgR hpq hpR).1
  · intro q hq hgq hpq
    let := hq
    exact (hX.component_splice_distance K n hn a π hg hp κ hκ hκ0 hD
      (πn.map (subpath 0 midpointTime)) q hgL hgq hpL hpq).2

theorem NoncollapsedRCD.exists_length_bounded_half_nodes
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    {D : ℝ} (hD0 : 0≤D) (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    ∃ a₀ a₁ : RenyiTransportNode n X,
      a₀.left=(κ univ)⁻¹ • κ.map (fun γ => γ 0) ∧
      a₀.right=(κ univ)⁻¹ • κ.map (fun γ => γ midpointTime) ∧
      a₁.left=(κ univ)⁻¹ • κ.map (fun γ => γ midpointTime) ∧
      a₁.right=(κ univ)⁻¹ • κ.map (fun γ => γ 1) ∧
      a₀.distance=D/2 ∧ a₁.distance=D/2 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  obtain ⟨a₀,a₁,h0,hm0,hm1,h1,_,_⟩ :=
    exists_normalized_subplan_half_nodes a π hg hp hC hcomp κ hκ hκ0
  have hd := hX.component_half_distance_bounds K n hn a π hg hp κ hκ hκ0 hD
  let b₀ : RenyiTransportNode n X := { a₀ with
    distance := D/2
    distance_nonneg := div_nonneg hD0 (by norm_num)
    distance_bound := by rw [h0,hm0]; exact hd.1 }
  let b₁ : RenyiTransportNode n X := { a₁ with
    distance := D/2
    distance_nonneg := div_nonneg hD0 (by norm_num)
    distance_bound := by rw [hm1,h1]; exact hd.2 }
  exact ⟨b₀,b₁,h0,hm0,hm1,h1,rfl,rfl⟩

end RegularPointCoordinates

end

end OAI
