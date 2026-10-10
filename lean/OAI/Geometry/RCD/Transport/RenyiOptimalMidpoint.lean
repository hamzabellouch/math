import OAI.Geometry.RCD.Transport.RenyiSemicontinuity

namespace OAI

/-! # Rényi-maximizing optimal midpoints

Compactness of actual optimal geodesic plans and the full-measure dual
formula give maximizers without assuming a density for the maximizer.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_optimal_geodesic_plan_maximizing_renyi [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (ν₀ ν₁ : ProbabilityMeasure X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (h1 : ∀ᵐ x ∂(ν₁ : Measure X), dist x p ≤ R)
    (hne : (OptimalGeodesicPlans ν₀ ν₁).Nonempty)
    (t : Time) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ π ∈ OptimalGeodesicPlans ν₀ ν₁, ∀ κ ∈ OptimalGeodesicPlans ν₀ ν₁,
      (∫ x, (((κ : Measure C(Time,X)).map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ) ≤
        ∫ x, (((π : Measure C(Time,X)).map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ := by
  have hc := isCompact_optimal_geodesic_plans ν₀ ν₁ p hR h0 h1
  have hmap : Continuous (fun π : ProbabilityMeasure C(Time,X) => π.map (fun γ => γ t)) :=
    ProbabilityMeasure.continuous_map (continuous_eval_const t)
  have hu := (upperSemicontinuous_renyiPower μ hq0 hq1).comp hmap
  obtain ⟨π,hπ,hm⟩ := (hu.upperSemicontinuousOn (OptimalGeodesicPlans ν₀ ν₁)).exists_isMaxOn hne hc
  refine ⟨π,hπ,fun κ hκ => ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ =>
    Real.rpow_nonneg ENNReal.toReal_nonneg q)).mp (hm hκ)

theorem NoncollapsedRCD.exists_renyi_maximizing_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))) ∧
      ∀ κ : Measure C(Time,X), IsProbabilityMeasure κ →
        (∀ᵐ γ ∂κ, IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))) →
        (∫ x, ((κ.map (fun γ => γ midpointTime)).rnDeriv
          ((hausdorff n X).restrict (closedBall p (3*R))) x).toReal^q
          ∂((hausdorff n X).restrict (closedBall p (3*R)))) ≤
        ∫ x, ((π.map (fun γ => γ midpointTime)).rnDeriv
          ((hausdorff n X).restrict (closedBall p (3*R))) x).toReal^q
          ∂((hausdorff n X).restrict (closedBall p (3*R))) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3*R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3*R)) isBounded_closedBall⟩
  obtain ⟨κ,hκ,hgκ,hpκ,_⟩ := hX.exists_compressed_midpoint K n hn ν₀ ν₁
    hC₀ h0 h1 hm0 hm1 p hR hs0 hs1
  let := hκ
  let v0 : ProbabilityMeasure X := ⟨ν₀,inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁,inferInstance⟩
  obtain ⟨π,hπ,hmax⟩ := exists_optimal_geodesic_plan_maximizing_renyi μ v0 v1 p
    hR hs0 hs1 ⟨⟨κ,hκ⟩,hgκ,hpκ⟩ midpointTime hq0 hq1
  exact ⟨π,inferInstance,hπ.1,hπ.2,fun κ' hκ' hgκ' hpκ' =>
    hmax ⟨κ',hκ'⟩ ⟨hgκ',hpκ'⟩⟩

end RegularPointCoordinates

end

end OAI
