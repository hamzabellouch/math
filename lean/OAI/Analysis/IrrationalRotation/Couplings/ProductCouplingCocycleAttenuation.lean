import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCocycleBounds
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalEvents

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.OrderedProductCoupling

theorem finite_cocycle_conditional_attenuation (P : Parameters)
    (hsum : Summable (energyBound P))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    (hwidth : ∀ i ∈ I, w i = P.a i ∨ w i = P.b i)
    (hthreshold : ∀ i ∈ I,
      w i ≤ 1 - Int.fract ((k : ℝ) * θ i) ∧
        1 - Int.fract ((k : ℝ) * θ i) ≤ 1 - w i)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (hrho : ∀ i ∈ I, ρ ≤ CouplingMarginalBounds.rho (P.κ i) (P.m i) (w i))
    (hcost : ∀ i ∈ I, L ≤ c i) :
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
  have hbound := ae_all_int_cocycle_ratio_bounds P hsum θ c hθ0 hθ hc
  apply finite_threshold_attenuation P I
    (fun i => 1 - Int.fract ((k : ℝ) * θ i)) w hwidth hthreshold
    m ρ L hρ hL hI hrho
    (fun ω => ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω) /
      ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω))
    (hbound.mono (fun _ h => (h k).2.1))
  filter_upwards [hbound] with ω hω
  intro i hi hcross
  exact ((hω k).2.2 i hcross).trans
    (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.OrderedProductCoupling

end

end OAI
