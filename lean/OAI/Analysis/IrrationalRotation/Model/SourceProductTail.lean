import OAI.Analysis.IrrationalRotation.Model.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Model.ProductCocycle
import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.OrderedProductCoupling

def SourceTailEstimate (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (j : ℕ) (P : Parameters) : Prop :=
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂law P, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        ((law P)[(H₁ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((law P)[(H₂ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((∃ i ∈ ProductPhases.consecutiveBlock p.m j,
          circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
          1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleRightEndpoint ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleLeftEndpoint ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω))

end Invariant233.OrderedProductCoupling

end

end OAI
