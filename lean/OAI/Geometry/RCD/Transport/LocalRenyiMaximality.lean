import OAI.Geometry.RCD.Transport.RenyiSubplanMaximality

namespace OAI

/-! # Localizing the reference measure without changing maximality -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [BorelSpace X] in
theorem RenyiMaximizingPlan.local_of_global (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    {ν₀ ν₁ : Measure X} {π : Measure C(Time,X)} [IsProbabilityMeasure π]
    {t : Time} {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan μ ν₀ ν₁ π t q)
    (hsπ : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B)
    (hs : ∀ κ : Measure C(Time,X), IsProbabilityMeasure κ →
      (∀ᵐ γ ∂κ, IsGeodesic γ) → IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))) →
      ∀ᵐ x ∂κ.map (fun γ => γ t), x∈B) :
    RenyiMaximizingPlan (μ.restrict B) ν₀ ν₁ π t q := by
  intro κ hκ hgκ hpκ
  let := hκ
  rw [←(renyiPower_localized μ _ hB (hs κ hκ hgκ hpκ) hq0 hq1.le).2,
    ←(renyiPower_localized μ _ hB hsπ hq0 hq1.le).2]
  exact hmax κ hκ hgκ hpκ

theorem NoncollapsedRCD.renyiNode_localMaximal
    (K : ℝ) (n : ℕ) (_hn : 2≤n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1) (a : RenyiTransportNode n X)
    (s : RenyiNodeSplit K q a) :
    RenyiMaximizingPlan ((hausdorff n X).restrict (closedBall a.center (3*a.radius)))
      a.left a.right s.plan midpointTime q := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let := s.probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (κ : Measure C(Time,X)) (hg : ∀ᵐ γ ∂κ, IsGeodesic γ)
      (hp : IsOptimalCoupling a.left a.right (κ.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂κ.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right κ hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 midpointTime)
  exact s.maximal.local_of_global μ measurableSet_closedBall hq0 hq1
    (hs s.plan s.geodesic s.optimal) (fun κ _ hg hp => hs κ hg hp)

end RegularPointCoordinates

end

end OAI
