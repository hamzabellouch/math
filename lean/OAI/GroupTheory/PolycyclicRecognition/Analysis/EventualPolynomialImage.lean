import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveParameterSets
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SubmersivePolynomialImage

namespace OAI

/-! # Eventual positivity suffices for the actual sampled image theorem -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_submersive_polynomial_image_eventual
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℝ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin m → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℝ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) := by
  obtain ⟨E', hE', hER', hm', hlower', heq⟩ :=
    exists_positive_parameter_sets (lt_of_lt_of_le zero_lt_one hR) E hE hER hmlower
  obtain ⟨C, hC, hCE, hlower⟩ := converging_submersive_polynomial_image
    rem hn f hf hpoly S hS b hb b₀ hb₀ hlim R hR t₀ ht₀ hs E' hE' hER' hm' hlower'
  refine ⟨C, hC, ?_, hlower⟩
  filter_upwards [hCE, heq] with r hr he
  simpa only [he] using hr

end PolycyclicRecognition

end

end OAI
