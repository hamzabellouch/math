import OAI.Analysis.IrrationalRotation.Model.SourceCouplingMarginals
import OAI.Analysis.IrrationalRotation.Couplings.BlockProductCoupling
import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCocycleAttenuation

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.OrderedProductCoupling

theorem sourceBlocks_energy_summable
    (M : ℕ → ℕ) (a b : ℕ → ℝ) (hM : ∀ s, 100 ≤ M s)
    (ha : ∀ s, 1 / (M s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (M s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (M s)) (tag : ℕ) :
    Summable (energyBound (sourceBlocks M a b hM ha ha' hb hb' e tag)) :=
  (ofBlocks_energy_sum M sourceKappa a b sourceKappa_nonneg sourceKappa_le hM
    ha ha' hb hb' e tag summable_sourceKappa_sq).1

theorem source_finite_cocycle_conditional_attenuation
    (M : ℕ → ℕ) (a b : ℕ → ℝ) (hM : ∀ s, 100 ≤ M s)
    (ha : ∀ s, 1 / (M s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (M s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (M s)) (tag : ℕ)
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    (hwidth : ∀ i ∈ I, w i = a (e i).1 ∨ w i = b (e i).1)
    (hthreshold : ∀ i ∈ I,
      w i ≤ 1 - Int.fract ((k : ℝ) * θ i) ∧
        1 - Int.fract ((k : ℝ) * θ i) ≤ 1 - w i)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (hrho : ∀ i ∈ I,
      ρ ≤ CouplingMarginalBounds.rho (sourceKappa (e i).1) (M (e i).1) (w i))
    (hcost : ∀ i ∈ I, L ≤ c i) :
    let P := sourceBlocks M a b hM ha ha' hb hb' e tag
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law P, ((law P)[H₁.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap leftEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, ((law P)[H₂.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap rightEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P,
        ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
          ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω) ≤
            Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
              H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  exact finite_cocycle_conditional_attenuation
    (sourceBlocks M a b hM ha ha' hb hb' e tag)
    (sourceBlocks_energy_summable M a b hM ha ha' hb hb' e tag)
    θ c hθ0 hθ hc k I w hwidth hthreshold m ρ L hρ hL hI hrho hcost

end Invariant233.OrderedProductCoupling

end

end OAI
