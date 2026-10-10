import OAI.GroupTheory.PolycyclicRecognition.Analysis.EventualPolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GrowingPositiveParameters
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GrowingSubmersivePolynomialImage

namespace OAI

/-! # Growing-cube image volume for successful measurable parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem converging_submersive_polynomial_image_growing_eventual_sequence
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (t₀ : Fin m → ℝ) (ht₀ : ∀ r, ‖t₀‖ ≤ R r)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨E', hE', hER', hm', hlower', heq⟩ :=
    exists_positive_parameter_sets_growing_sequence R scale
      (fun r => lt_of_lt_of_le zero_lt_one (hR r)) E hE hER hmlower
  obtain ⟨C, hC, hCE, hlower⟩ := converging_submersive_polynomial_image_growing_sequence
    scale hscale rem hn f hf hpoly S hS b hb b₀ hb₀ hlim R hR hRupper t₀ ht₀ hs E' hE' hER' hm' hlower'
  refine ⟨C, hC, ?_, hlower⟩
  filter_upwards [hCE, heq] with r hr he
  simpa only [he] using hr

end PolycyclicRecognition

end

end OAI
