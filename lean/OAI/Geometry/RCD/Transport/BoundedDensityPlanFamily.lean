import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Actual bounded-compression plans for a sequence of bounded density pairs -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.bounded_density_plan_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (p : ℕ → X) (R : ℕ → ℝ) (hR : ∀ k, 0≤R k)
    (ν₀ ν₁ : ℕ → ProbabilityMeasure X) (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k≠⊤)
    (h0 : ∀ k, (ν₀ k : Measure X)≤C k • hausdorff n X)
    (h1 : ∀ k, (ν₁ k : Measure X)≤C k • hausdorff n X)
    (hs0 : ∀ k, ∀ᵐ x ∂(ν₀ k : Measure X), dist x (p k)≤R k)
    (hs1 : ∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), dist x (p k)≤R k) :
    ∃ P : ℕ → ProbabilityMeasure C(Time,X),
      (∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), IsGeodesic γ) ∧
      (∀ k, IsOptimalCoupling (ν₀ k) (ν₁ k)
        ((P k : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))) ∧
      (∀ k, Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2)
        (P k : Measure C(Time,X))) ∧
      (∀ k t, (P k : Measure C(Time,X)).map (fun γ => γ t)≤
        compressionBudget K n (2*R k) (C k) • hausdorff n X) := by
  choose π hπ hgeo hopt hi hcomp using fun k =>
    hX.exists_bounded_entropy_plan K n hn (ν₀ k : Measure X) (ν₁ k : Measure X)
      (hC k) (h0 k) (h1 k) (p k) (hR k) (hs0 k) (hs1 k)
  exact ⟨fun k => ⟨π k,hπ k⟩,hgeo,hopt,hi,fun k t => (hcomp k t).1⟩

end RegularPointCoordinates

end

end OAI
