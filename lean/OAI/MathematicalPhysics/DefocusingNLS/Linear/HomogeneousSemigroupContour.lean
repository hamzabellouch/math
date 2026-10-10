import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSemigroupDecay

namespace OAI

/-! # The contour decomposition of a strongly continuous semigroup

The algebra and compact-interval argument are performed before specializing
its Banach space and parameters to the physical matched profile.
-/

open scoped NNReal

namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem semigroup_contour_decomposition (S : ℝ≥0 → E →L[ℂ] E)
    (hzero : S 0 = 1) (hadd : ∀ s t, S (s + t) = S t * S s)
    (hS : ∀ x : E, Continuous (fun t => S t x))
    (τ : ℝ≥0) (hτ : 0 < τ) (B K : E →L[ℂ] E)
    (hstep : S τ = B + K) (hB : ‖B‖ < 1)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (η : ℝ) (hη : η < 1) :
    ∃ r : ℝ, η < r ∧ r < 1 ∧ ∃ Q : E →L[ℂ] E,
      IsIdempotentElem Q ∧ FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
      (∀ s, Commute (S s) Q) ∧
      ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ s : ℝ≥0, ∀ u, Q u = 0 →
        ‖S s u‖ ≤ D * Real.exp (-δ * (s : ℝ)) * ‖u‖ := by
  obtain ⟨r, hηr, hr0, hr, Q, hQ, hfin, hcomm, C, hC, hpowers⟩ :=
    finiteRank_contour_decomposition B K hB hK η hη
  refine ⟨r, hηr, hr, Q, hQ, hfin, ?_, ?_⟩
  · intro s
    apply hcomm
    rw [← hstep]
    change S s * S τ = S τ * S s
    rw [← hadd, ← hadd, add_comm s τ]
  · apply continuous_decay_of_step_decay S hzero hadd hS
      {u | Q u = 0} τ hτ r C hr0 hr hC
    intro j u hu
    simpa only [hstep] using hpowers j u hu

end DefocusingNLS

end OAI
