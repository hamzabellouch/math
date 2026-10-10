import OAI.Analysis.IrrationalRotation.Rotation.CircleTailAttenuation

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

theorem tail_exceptional_families_of_subset
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    (j : ℕ) (hj : 1 ≤ j) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (E : Set Sample) (hEm : MeasurableSet E) (hE : E ⊆ tagEvent p j) :
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ k : ℤ, (p.K j : ℤ) < |k| → ∀ᵐ ω ∂law p j,
        ((law p j)[(H₁ k).indicator (fun _ => (1 : ℝ)) | endpointSigma p hr false]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ k : ℤ, (p.K j : ℤ) < |k| → ∀ᵐ ω ∂law p j,
        ((law p j)[(H₂ k).indicator (fun _ => (1 : ℝ)) | endpointSigma p hr true]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂(law p j).restrict E, ∀ k : ℤ, (p.K j : ℤ) < |k| →
        p.floorCocycle θ k (point p hr true ω) /
          p.floorCocycle θ k (point p hr false ω) ≤
          Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
            (H₂ k).indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  let I := {k : ℤ // (p.K j : ℝ) < |(k : ℝ)|}
  have hex (k : I) := actual_tail_attenuation hp j hj hr k.1 k.2
  choose H₁ H₂ hm₁ hm₂ hc₁ hc₂ hb using hex
  let A₁ : ℤ → Set Sample := fun k =>
    if hk : (p.K j : ℝ) < |(k : ℝ)| then H₁ ⟨k, hk⟩ else ∅
  let A₂ : ℤ → Set Sample := fun k =>
    if hk : (p.K j : ℝ) < |(k : ℝ)| then H₂ ⟨k, hk⟩ else ∅
  have hreal (k : ℤ) (hk : (p.K j : ℤ) < |k|) :
      (p.K j : ℝ) < |(k : ℝ)| := by exact_mod_cast hk
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [A₁]
    split_ifs with hk
    · exact hm₁ ⟨k, hk⟩
    · exact MeasurableSet.empty
  · intro k
    dsimp [A₂]
    split_ifs with hk
    · exact hm₂ ⟨k, hk⟩
    · exact MeasurableSet.empty
  · intro k hk
    simpa only [A₁, dite_eq_left (hreal k hk)] using hc₁ ⟨k, hreal k hk⟩
  · intro k hk
    simpa only [A₂, dite_eq_left (hreal k hk)] using hc₂ ⟨k, hreal k hk⟩
  · have hall := ae_all_iff.mpr hb
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hEm] with ω hω hmem
    intro k hk
    simpa only [A₁, A₂, dite_eq_left (hreal k hk)] using
      hω ⟨k, hreal k hk⟩ (hE hmem)

end Invariant233.CircleCoupling

end

end OAI
