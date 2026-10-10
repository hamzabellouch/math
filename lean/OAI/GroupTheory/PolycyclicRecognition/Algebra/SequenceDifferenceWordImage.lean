import OAI.GroupTheory.PolycyclicRecognition.Algebra.DifferenceAmplitudeWord
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSubmersivePolynomialImage

namespace OAI

/-! # One fixed switch scheme retains volume on every sufficiently large good set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter Module
open scoped Topology

theorem differenceWord_subexponential_image_sequence
    {I : Type*} [Fintype I] {n m c : ℕ}
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
    (E : ℕ → Set (Fin (m + m) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ differenceAmplitudeWordEndpoint a letters (b r) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  exact converging_submersive_polynomial_image_sequence scale hscale rem hn
    (fun z => differenceAmplitudeWordEndpoint a letters z.1 z.2)
    (contDiff_differenceAmplitudeWord a letters)
    (hasPolynomialCoordinates_differenceAmplitudeWord a letters)
    S hS b hb b₀ hb₀ hlim R hR t₀ ht₀ hs E hE hER hm hmlower

/-- The scheme is fixed before the successful parameter sets are selected.
Its limiting rank follows from the generating Lie words, not from any premise
on the restricted endpoint images. -/
theorem exists_fixed_differenceWord_image_sequence
    {I J : Type*} [Fintype I] {n c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (hB : IsLieBracket b₀.1) (hg : PolynomialGroupLaws (dynkinProduct a b₀.1))
    (hc : ExponentialConjugationLaw (dynkinProduct a b₀.1) b₀.1)
    (basis : Basis J ℝ (Fin n → ℝ)) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBilinearWord b₀.1 b₀.2 (words j) = basis j) :
    ∃ (m : ℕ) (letters : Fin m → I) (R₀ : ℝ), 1 ≤ R₀ ∧
      ∀ R ≥ R₀, ∀ E : ℕ → Set (Fin (m + m) → ℝ),
        (∀ r, MeasurableSet (E r)) → (∀ r, E r ⊆ closedBall 0 R) →
        (∀ r, 0 < (volume (E r)).toReal) →
        HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal) →
        ∃ C : ℕ → Set (Fin n → ℝ),
          (∀ r, IsCompact (C r)) ∧
          (∀ᶠ r in atTop, C r ⊆ differenceAmplitudeWordEndpoint a letters (b r) '' E r) ∧
          HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨m, letters, t₀, _, hs⟩ := exists_submersive_differenceAmplitudeWord
    a b₀.1 hB hg hc b₀.2 basis words hwords
  refine ⟨m, letters, max 1 ‖t₀‖, le_max_left _ _, ?_⟩
  intro R hR E hE hER hm hmlower
  exact differenceWord_subexponential_image_sequence scale hscale rem hn a letters S hS b hb b₀ hb₀ hlim
    R ((le_max_left _ _).trans hR) t₀ ((le_max_right _ _).trans hR) hs E hE hER hm hmlower

end PolycyclicRecognition

end

end OAI
