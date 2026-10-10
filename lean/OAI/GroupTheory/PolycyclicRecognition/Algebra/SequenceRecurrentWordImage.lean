import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecurrentWordImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSuccessfulParameterMass
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSuccessfulWordImage

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem recurrent_differenceWord_image_sequence
    {I G : Type*} [Fintype I] [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] {n m c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters b₀) t₀))
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ x ∈ Q r, ∀ s ∈ K r j, x * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (C : ℕ → Set (Fin n → ℝ)),
      (∀ r, x r ∈ A r) ∧ (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
        SwitchSuccessful (fun _ => A r) 0 m (x r) (sampledSwitchParameters (sample r) m t) ∧
        differenceAmplitudeWordEndpoint a letters (b r) t = y := by
  obtain ⟨x, E, hx, hE, hprob, hsuccess⟩ := exists_subexponential_successful_parameters_sequence
    scale hscale μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol m hA hAQ hApos hAlower hDupper
  obtain ⟨C, hC, hCvol, hgood⟩ := successful_differenceWord_image_sequence
    scale hscale rem hn a letters S hS b hb b₀ hb₀ hlim ρ hρ t₀ ht₀ hs
    sample σ hsample x A E hE hprob hsuccess
  exact ⟨x, C, hx, hC, hCvol, hgood⟩

end PolycyclicRecognition

end

end OAI
