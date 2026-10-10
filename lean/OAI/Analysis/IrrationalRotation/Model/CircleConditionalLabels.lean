import OAI.Analysis.IrrationalRotation.Model.CircleCoupling
import Mathlib.Probability.Independence.Conditional

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData CouplingMarginalBounds

structure ConditionalLabelLaws (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : Prop where
  probability : IsProbabilityMeasure (law p j)
  endpoint_measurable : ∀ side, Measurable (point p hr side)
  independent : letI := probability
    ∀ side, iCondIndepFun (MeasurableSpace.comap (point p hr side) inferInstance)
      (endpoint_measurable side).comap_le label (law p j)
  finite_posterior : ∀ side (S : Finset ℕ) (C : ℕ → Set Label),
    (∀ i, MeasurableSet (C i)) →
    (law p j)⟦(⋂ i ∈ S, label i ⁻¹' C i) |
      MeasurableSpace.comap (point p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => ∏ i ∈ S, (posterior p j side i
        (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr side ω) i)).real (C i))
  top_probability : ∀ s, 1 ≤ s → ∀ i ∈ p.block s, ∀ which,
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      p.coordinate i (point p hr false ω) < u → u ≤ 1 - width (p.a s) (p.b s) which →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {topLabel which} |
          MeasurableSpace.comap (point p hr false) inferInstance⟧) ω
  bottom_probability : ∀ s, 1 ≤ s → ∀ i ∈ p.block s, ∀ which,
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      u ≤ p.coordinate i (point p hr true ω) → width (p.a s) (p.b s) which ≤ u →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {bottomLabel which} |
          MeasurableSpace.comap (point p hr true) inferInstance⟧) ω
  top_forcing : ∀ s, 1 ≤ s → ∀ i ∈ p.block s, ∀ which,
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = topLabel which →
      u ≤ 1 - width (p.a s) (p.b s) which → u ≤ p.coordinate i (point p hr true ω)
  bottom_forcing : ∀ s, 1 ≤ s → ∀ i ∈ p.block s, ∀ which,
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = bottomLabel which →
      width (p.a s) (p.b s) which ≤ u → p.coordinate i (point p hr false ω) < u

end Invariant233.CircleCoupling

end

end OAI
