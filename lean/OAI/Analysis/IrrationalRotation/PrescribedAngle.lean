import OAI.Analysis.IrrationalRotation.PrescribedAngleConditional

namespace OAI

/-! Continuous counterexamples for every prescribed irrational angle. -/

namespace Invariant233

theorem publishedRotationSpectralInput_of_irrational {θ : ℝ} (hθ : Irrational θ) :
    PublishedRotationSpectralInput θ := by
  refine ⟨fun f hf => ?_⟩
  rw [spectralRadius_eq_of_unital, Rotation.weightedReal_spectrum hθ f hf]
  simp

namespace Results

theorem prescribed_irrational_counterexample (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ) :
    ∃ f : C(Circle, ℝ), Rotation.IsContinuousCounterexample θ f :=
  prescribed_irrational_counterexample_of_published_spectral_input θ hθ
    (publishedRotationSpectralInput_of_irrational hθ)

theorem prescribed_irrational_weight (θ : ℝ) (hθ : Irrational θ) :
    ∃ f : C(Circle, ℝ),
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, f x = 0 ↔ x = 0) ∧
      HasNegInfiniteLogIntegral circleMeasure f ∧
      ∀ P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert,
        P ∈ Rotation.algebra θ → IsStarProjection P →
        (1 - P) * Rotation.weightedReal θ f * P = 0 → P = 0 ∨ P = 1 := by
  obtain ⟨f, hf, _, hinv, _⟩ :=
    prescribed_irrational_counterexample_of_published_spectral_input θ hθ
      (publishedRotationSpectralInput_of_irrational hθ)
  exact ⟨f, hf.2.1, hf.2.2.1, hf.2.2.2, hinv⟩

end Results
end Invariant233

end OAI
