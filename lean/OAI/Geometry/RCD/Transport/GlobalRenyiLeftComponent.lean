import OAI.Geometry.RCD.Transport.RenyiLeftComponent
import OAI.Geometry.RCD.Transport.LocalRenyiMaximality

namespace OAI

/-! # Global-reference maximality of normalized left length components

A single bounded reference region contains all relevant midpoint measures.
Localizing and then restoring the Hausdorff reference preserves the actual
variational comparison, including possible singular competitors.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.global_renyi_left_component
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan (hausdorff n X)
      (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (π.map (subpath 0 midpointTime)) midpointTime q) :
    RenyiMaximizingPlan (hausdorff n X) ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime))
      ((κ univ)⁻¹ • κ.map (subpath 0 midpointTime)) midpointTime q := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*(3*a.radius))
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  let : NeZero κ := ⟨by intro he; apply hκ0; rw [he]; rfl⟩
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πL := π.map (subpath 0 midpointTime)
  obtain ⟨hπL,hgL,hpL⟩ := geodesic_subpath_law π hg hpp hfin 0 midpointTime
  let : IsProbabilityMeasure πL := hπL
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), dist x a.center≤3*a.radius := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  have hsN (t : Time) : ∀ᵐ x ∂((κ univ)⁻¹ • κ.map (fun γ => γ t)), dist x a.center≤3*a.radius :=
    ((hs t).filter_mono (Measure.map_mono hκ (measurable_path_eval t)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le
  have hstay (ν₀ ν₁ : Measure X) (h0 : ∀ᵐ x ∂ν₀, dist x a.center≤3*a.radius)
      (h1 : ∀ᵐ x ∂ν₁, dist x a.center≤3*a.radius)
      (η : Measure C(Time,X)) (hge : ∀ᵐ γ ∂η, IsGeodesic γ)
      (hpe : IsOptimalCoupling ν₀ ν₁ (η.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂η.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ η hge hpe a.center
      (mul_nonneg (by norm_num) a.radius_nonneg) h0 h1).mono (fun γ hγ => hγ.2 midpointTime)
  have hml := hmax.local_of_global μ measurableSet_closedBall hq0 hq1
    (hstay _ _ (hs 0) (hs midpointTime) πL hgL hpL)
    (fun η _ hge hpe => hstay _ _ (hs 0) (hs midpointTime) η hge hpe)
  have hmc := hX.renyi_left_length_component_maximal K n hn a.left a.right
    (Measure.absolutelyContinuous_of_le_smul a.left_bound) a.center a.radius_nonneg
    a.left_support a.right_support (μ.restrict B) π hg hp hS κ hκeq hκ0 hq0 hq1 hml
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,hfn⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  obtain ⟨hnL,hgnL,hpnL⟩ := geodesic_subpath_law πn hgn hpn hfn 0 midpointTime
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  have hmap : πn.map (subpath 0 midpointTime)=(κ univ)⁻¹ • κ.map (subpath 0 midpointTime) :=
    Measure.map_smul _ (subpath_measurable 0 midpointTime).aemeasurable
  rw [hmap] at hnL hgnL hpnL
  rw [heval,heval] at hpnL
  let := hnL
  exact hmc.global_of_local μ measurableSet_closedBall hq0 hq1
    (hstay _ _ (hsN 0) (hsN midpointTime) _ hgnL hpnL)
    (fun η _ hge hpe => hstay _ _ (hsN 0) (hsN midpointTime) η hge hpe)

end RegularPointCoordinates

end

end OAI
