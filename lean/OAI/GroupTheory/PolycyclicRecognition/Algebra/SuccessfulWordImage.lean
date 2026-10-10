import OAI.GroupTheory.PolycyclicRecognition.Analysis.EventualPolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DifferenceWordImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SampledSuccessfulVolume

namespace OAI

/-! # Compact endpoint volume with every intermediate sheet still good -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem successful_differenceWord_image
    {I G : Type*} [Fintype I] [Group G] [MeasurableSpace G] {n m c : ℕ}
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℝ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters b₀) t₀))
    (sample : ℝ → ℕ → ℝ → G) (σ : ℝ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw R) (σ r j))
    (x : ℝ → G) (A : ℝ → Set G) (E : ℝ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBound (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) R,
        SwitchSuccessful (fun _ => A r) 0 m (x r) (sampledSwitchParameters (sample r) m t) ∧
        differenceAmplitudeWordEndpoint a letters (b r) t = y := by
  obtain ⟨F, hF, hFR, hFvol, hFs⟩ := exists_sampled_success_volume
    (lt_of_lt_of_le zero_lt_one hR) m sample σ hsample x A E hE hprob hsuccess
  obtain ⟨C, hC, hCF, hCvol⟩ := converging_submersive_polynomial_image_eventual
    rem hn (fun z => differenceAmplitudeWordEndpoint a letters z.1 z.2)
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
