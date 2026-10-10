import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationEvent
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingOrder

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma endpoint_absolutelyContinuous (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    (law p j).map (point p hr side) ≪ circleMeasure := by
  obtain ⟨H, _, _, _, _, hH⟩ := endpoint_density hp j hr side
  rw [hH]
  exact withDensity_absolutelyContinuous _ _

theorem actual_tail_attenuation (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : TailAttenuation θ p j hr :=
  actual_tail_attenuation_of_ac_order hp j hj hr
    (endpoint_absolutelyContinuous hp j hr)
    ((ae_coordinates_ordered hp j hr).mono (fun _ h i => h i.2))

theorem exists_actual_tail_attenuation (j : ℕ) (hj : 1 ≤ j) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i, TailAttenuation θ p j hr :=
  ⟨MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible,
    actual_tail_attenuation hp j hj _⟩

theorem tail_attenuation_on_truncationEvent (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ)
    (k : ℤ) (hk : (p.K j : ℝ) < |(k : ℝ)|) :
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₁.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr false]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₂.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr true]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j, ω ∈ truncationEvent p j hr r →
        p.floorCocycle θ k (point p hr true ω) /
          p.floorCocycle θ k (point p hr false ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  obtain ⟨H₁, H₂, hm₁, hm₂, hc₁, hc₂, hb⟩ := actual_tail_attenuation hp j hj hr k hk
  exact ⟨H₁, H₂, hm₁, hm₂, hc₁, hc₂,
    hb.mono (fun _ h he => h (truncationEvent_subset_tagEvent p j hr r he))⟩

end Invariant233.CircleCoupling

end

end OAI
