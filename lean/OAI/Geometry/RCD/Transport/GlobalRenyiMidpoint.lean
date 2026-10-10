import OAI.Geometry.RCD.Transport.ReducedMidpoint

namespace OAI

/-! # Reference-independent maximality for dyadic Rényi midpoints

Compactness used a finite restricted reference measure. Supported plans
have exactly the same power integral against the original reference, so
the maximizing property is independent of the containing support ball.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [BorelSpace X] in
theorem RenyiMaximizingPlan.global_of_local (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    {ν₀ ν₁ : Measure X} {π : Measure C(Time,X)} [IsProbabilityMeasure π]
    {t : Time} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmax : RenyiMaximizingPlan (μ.restrict B) ν₀ ν₁ π t q)
    (hsπ : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B)
    (hs : ∀ κ : Measure C(Time,X), IsProbabilityMeasure κ →
      (∀ᵐ γ ∂κ, IsGeodesic γ) → IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))) →
      ∀ᵐ x ∂κ.map (fun γ => γ t), x∈B) :
    RenyiMaximizingPlan μ ν₀ ν₁ π t q := by
  intro κ hκ hgκ hpκ
  let := hκ
  rw [(renyiPower_localized μ _ hB (hs κ hκ hgκ hpκ) hq0 hq1.le).2,
    (renyiPower_localized μ _ hB hsπ hq0 hq1.le).2]
  exact hmax κ hκ hgκ hpκ

theorem NoncollapsedRCD.exists_global_renyi_midpoint_short
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (D : ℝ) (hD : OptimalPlanDistanceBound ν₀ ν₁ D)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n D C • hausdorff n X ∧
      RenyiMaximizingPlan (hausdorff n X) ν₀ ν₁ π midpointTime q := by
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall p (3*R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hm0 := finiteSecondMoment_of_bounded ν₀ p hs0
  have hm1 := finiteSecondMoment_of_bounded ν₁ p hs1
  obtain ⟨π,hπ,hg,hp,hcap,hmax⟩ := hX.exists_compressed_renyi_maximizing_midpoint_short K n hn
    ν₀ ν₁ hC h0 h1 hm0 hm1 p hR hs0 hs1 D hD hq0 hq1
  let := hπ
  have hs (κ : Measure C(Time,X)) (hgκ : ∀ᵐ γ ∂κ, IsGeodesic γ)
      (hpκ : IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂κ.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ κ hgκ hpκ p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  exact ⟨π,hπ,hg,hp,hcap,hmax.global_of_local μ measurableSet_closedBall hq0 hq1
    (hs π hg hp) (fun κ _ hgκ hpκ => hs κ hgκ hpκ)⟩

end RegularPointCoordinates

end

end OAI
