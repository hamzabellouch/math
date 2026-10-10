import OAI.Analysis.IrrationalRotation.Product.ProductSourceCocycleAttenuation
import OAI.Analysis.IrrationalRotation.Product.ProductCircleConditioning

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.OrderedProductCoupling

theorem source_finite_cocycle_conditional_attenuation_circle
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
        MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, ((law P)[H₂.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P,
        ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
          ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω) ≤
            Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
              H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  let P := sourceBlocks M a b hM ha ha' hb hb' e tag
  obtain ⟨H₁, H₂, hmeas₁, hmeas₂, hbound₁, hbound₂, hratio⟩ :=
    source_finite_cocycle_conditional_attenuation M a b hM ha ha' hb hb' e tag
      θ c hθ0 hθ hc k I w hwidth hthreshold m ρ L hρ hL hI hrho hcost
  refine ⟨H₁, H₂, hmeas₁, hmeas₂, ?_, ?_, hratio⟩
  · filter_upwards [hbound₁, left_condExp_eq_circle P (H₁.indicator (fun _ => (1 : ℝ)))]
      with ω hω heq
    rw [← heq]
    exact hω
  · filter_upwards [hbound₂, right_condExp_eq_circle P (H₂.indicator (fun _ => (1 : ℝ)))]
      with ω hω heq
    rw [← heq]
    exact hω

end Invariant233.OrderedProductCoupling

end

end OAI
