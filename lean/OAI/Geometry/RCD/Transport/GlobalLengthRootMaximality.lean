import OAI.Geometry.RCD.Transport.LengthRootMaximality
import OAI.Geometry.RCD.Transport.LocalRenyiMaximality
import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan

namespace OAI

/-! # Length-component maximality with the original Hausdorff reference -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.global_root_length_component
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan (hausdorff n X) a.left a.right π midpointTime q) :
    RenyiMaximizingPlan (hausdorff n X) ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) ((κ univ)⁻¹ • κ) midpointTime q := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  have hstay (ν₀ ν₁ : Measure X) (h0 : ∀ᵐ x ∂ν₀, dist x a.center≤a.radius)
      (h1 : ∀ᵐ x ∂ν₁, dist x a.center≤a.radius)
      (η : Measure C(Time,X)) (hge : ∀ᵐ γ ∂η, IsGeodesic γ)
      (hpe : IsOptimalCoupling ν₀ ν₁ (η.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂η.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ η hge hpe a.center a.radius_nonneg h0 h1).mono
      (fun γ hγ => hγ.2 midpointTime)
  have hml := hmax.local_of_global μ measurableSet_closedBall hq0 hq1
    (hstay _ _ a.left_support a.right_support π hg hp)
    (fun η _ hge hpe => hstay _ _ a.left_support a.right_support η hge hpe)
  have hm := hX.renyi_root_length_component_maximal K n hn a π hg hp hC hc
    (μ.restrict B) hS κ hκeq hκ0 hq0 hq1 hml
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,_⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  rw [heval,heval] at hpn
  have hsN (t : Time) (ht : t=0 ∨ t=1) :
      ∀ᵐ x ∂((κ univ)⁻¹ • κ.map (fun γ => γ t)), dist x a.center≤a.radius := by
    have hs : ∀ᵐ x ∂π.map (fun γ => γ t), dist x a.center≤a.radius := by
      rcases ht with rfl | rfl
      · rw [he.1]; exact a.left_support
      · rw [he.2]; exact a.right_support
    exact (hs.filter_mono (Measure.map_mono hκ (measurable_path_eval t)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le
  exact hm.global_of_local μ measurableSet_closedBall hq0 hq1
    (hstay _ _ (hsN 0 (Or.inl rfl)) (hsN 1 (Or.inr rfl)) πn hgn hpn)
    (fun η _ hge hpe => hstay _ _ (hsN 0 (Or.inl rfl)) (hsN 1 (Or.inr rfl)) η hge hpe)

end RegularPointCoordinates

end

end OAI
