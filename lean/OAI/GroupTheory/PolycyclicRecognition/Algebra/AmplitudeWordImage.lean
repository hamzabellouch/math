import OAI.GroupTheory.PolycyclicRecognition.Algebra.AmplitudeWordCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConvergingPolynomialImage

namespace OAI

/-! # Compact image volume for the independently sampled generator word -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem amplitudeWord_subexponential_image
    {I : Type*} [Fintype I] {n k c : ℕ}
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin (n + k) → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℝ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R)
    (hdet : (fderiv ℝ (fun v => amplitudeWordEndpoint a letters b₀ (Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℝ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ amplitudeWordEndpoint a letters (b r) '' E r) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) := by
  exact converging_smooth_polynomial_family_image rem n k hn
    (fun z => amplitudeWordEndpoint a letters z.1 z.2)
    (contDiff_amplitudeWordEndpoint a letters)
    (hasPolynomialCoordinates_amplitudeWordEndpoint a letters)
    S hS b hb b₀ hb₀ hlim R hR v₀ z₀ hanchor hdet E hE hER hm hmlower

end PolycyclicRecognition

end

end OAI
