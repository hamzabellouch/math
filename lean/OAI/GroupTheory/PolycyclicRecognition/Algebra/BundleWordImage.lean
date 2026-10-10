import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleWordRank
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GrowingEventualPolynomialImage

namespace OAI

/-! # Correlated successful parameters for the joint source-bundle map -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem bundle_word_image_sequence {I : Type*} [Fintype I] {n m h c M N : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ N)
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : ℕ → WordLawData I n) (p₀ : WordLawData I n) (hlim : Tendsto p atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hanchor : ∀ r, ‖input.symm (fun _ => t₀)‖ ≤ R r)
    (A : ℕ → Set (Fin M → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set (Fin N → ℝ), (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ bundleWordEndpoint a letters input output (p r) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  exact converging_submersive_polynomial_image_growing_eventual_sequence scale hscale rem hN
    (fun z => bundleWordEndpoint a letters input output z.1 z.2)
    (contDiff_bundleWordEndpoint a letters input output)
    (hasPolynomialCoordinates_bundleWordEndpoint a letters input output)
    (insert p₀ (range p)) hlim.isCompact_insert_range p
    (fun r => mem_insert_of_mem _ (mem_range_self r)) p₀ (mem_insert _ _) hlim R hR hRupper
    (input.symm (fun _ => t₀)) hanchor
    (bundleWordEndpoint_submersive a letters input output p₀ t₀ hs) A hA hAR hAlower

end PolycyclicRecognition

end

end OAI
