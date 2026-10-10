import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalEvents
import OAI.Analysis.IrrationalRotation.Product.ProductCircleConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling

theorem finite_threshold_attenuation_circle (P : Parameters) (I : Finset ℕ)
    (u w : ℕ → ℝ)
    (hwidth : ∀ i ∈ I, w i = P.a i ∨ w i = P.b i)
    (hthreshold : ∀ i ∈ I, w i ≤ u i ∧ u i ≤ 1 - w i)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (hrho : ∀ i ∈ I, ρ ≤ CouplingMarginalBounds.rho (P.κ i) (P.m i) (w i))
    (R : Sample → ℝ) (hR : ∀ᵐ ω ∂law P, R ω ≤ 1)
    (hcross : ∀ᵐ ω ∂law P, ∀ i ∈ I,
      (leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i) → R ω ≤ Real.exp (-L)) :
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law P, ((law P)[H₁.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, ((law P)[H₂.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, R ω ≤ Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hleft, hright, hratio⟩ :=
    finite_threshold_attenuation P I u w hwidth hthreshold m ρ L hρ hL hI hrho
      R hR hcross
  refine ⟨H₁, H₂, hH₁, hH₂, ?_, ?_, hratio⟩
  · filter_upwards [hleft, left_condExp_eq_circle P (H₁.indicator (fun _ => (1 : ℝ)))]
      with ω hω heq
    rw [← heq]
    exact hω
  · filter_upwards [hright, right_condExp_eq_circle P (H₂.indicator (fun _ => (1 : ℝ)))]
      with ω hω heq
    rw [← heq]
    exact hω

end Invariant233.OrderedProductCoupling

end

end OAI
