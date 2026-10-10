import OAI.Analysis.IrrationalRotation.Model.CircleCoupling
import OAI.Analysis.IrrationalRotation.Model.ParameterCircleWeights
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.CircleCoupling

def tagEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  {ω | ∃ i ∈ p.block j, label i ω = some 4}

abbrev endpointSigma (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) : MeasurableSpace Sample :=
  MeasurableSpace.comap (point p hr side) inferInstance

def TailAttenuation (θ : ℝ) (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : Prop :=
  ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₁.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr false]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₂.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr true]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j, ω ∈ tagEvent p j →
        p.floorCocycle θ k (point p hr true ω) /
          p.floorCocycle θ k (point p hr false ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω)

end Invariant233.CircleCoupling

end

end OAI
