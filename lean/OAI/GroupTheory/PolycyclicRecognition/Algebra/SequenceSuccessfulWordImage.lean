import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulWordImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSampledSuccessfulVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSubmersivePolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceEventualPolynomialImage

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem successful_differenceWord_image_sequence
    {I G : Type*} [Fintype I] [Group G] [MeasurableSpace G] {n m c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters b₀) t₀))
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw R) (σ r j))
    (x : ℕ → G) (A : ℕ → Set G) (E : ℕ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) R,
        SwitchSuccessful (fun _ => A r) 0 m (x r) (sampledSwitchParameters (sample r) m t) ∧
        differenceAmplitudeWordEndpoint a letters (b r) t = y := by
  obtain ⟨F, hF, hFR, hFvol, hFs⟩ := exists_sampled_success_volume_sequence
    (lt_of_lt_of_le zero_lt_one hR) m scale hscale sample σ hsample x A E hE hprob hsuccess
  obtain ⟨C, hC, hCF, hCvol⟩ := converging_submersive_polynomial_image_eventual_sequence
    scale hscale rem hn (fun z => differenceAmplitudeWordEndpoint a letters z.1 z.2)
    (contDiff_differenceAmplitudeWord a letters)
    (hasPolynomialCoordinates_differenceAmplitudeWord a letters)
    S hS b hb b₀ hb₀ hlim R hR t₀ ht₀ hs F hF hFR hFvol
  refine ⟨C, hC, hCvol, ?_⟩
  filter_upwards [hCF] with r hr
  intro y hy
  obtain ⟨t, ht, he⟩ := hr hy
  exact ⟨t, hFR r ht, hFs r t ht, he⟩

end PolycyclicRecognition

end

end OAI
