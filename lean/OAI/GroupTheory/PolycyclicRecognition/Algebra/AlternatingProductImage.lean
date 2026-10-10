import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingPolynomialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GrowingEventualPolynomialImage

namespace OAI

/-! # Image volume for the limiting alternating product -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem alternating_product_image_growing_sequence
    {m n h c : ℕ} (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (p : ℕ → AlternatingLawData n) (p₀ : AlternatingLawData n)
    (hlim : Tendsto p atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin n → ℝ) × (Fin n → ℝ))
    (hs : Function.Surjective (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ flatAlternatingProduct a e (p r) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  let R' := fun r => R r + (1 + ‖e.symm z₀‖)
  have hR' (r : ℕ) : 1 ≤ R' r := by dsimp [R']; linarith [hR r, norm_nonneg (e.symm z₀)]
  have hRupper' : HasSubexponentialUpperBoundSeq scale R' :=
    hRupper.add (sequence_subexponential_upper_const hscale (1 + ‖e.symm z₀‖)) hscale
  apply converging_submersive_polynomial_image_growing_eventual_sequence scale hscale rem hn
    (fun z => flatAlternatingProduct a e z.1 z.2)
    (contDiff_flatAlternatingProduct a e) (hasPolynomialCoordinates_flatAlternatingProduct a e)
    (insert p₀ (range p)) hlim.isCompact_insert_range p
    (fun r => mem_insert_of_mem _ (mem_range_self r)) p₀ (mem_insert _ _) hlim
    R' hR' hRupper' (e.symm z₀) (fun r => by dsimp [R']; linarith [hR r])
    (flatAlternatingProduct_submersive a e p₀ z₀ hs) E hE _ hmlower
  intro r x hx
  apply mem_closedBall_zero_iff.mpr
  exact (mem_closedBall_zero_iff.mp (hER r hx)).trans
    (by dsimp [R']; linarith [norm_nonneg (e.symm z₀)])

end PolycyclicRecognition

end

end OAI
