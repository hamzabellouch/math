import OAI.Analysis.KadisonKastler.ExpectedMatrixStability
import OAI.Analysis.KadisonKastler.PublishedExpectedMatrixSubfactor

namespace OAI

/-! # Uniform stability using the actual expected matrix models

Expected matrix models supply the modular preparation data. The second
model supplies its normalized cyclic separating vector.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- The expected-matrix-model formulation keeps the tolerance independent
of both models and all represented algebras. -/
theorem uniform_expected_models_typeIII1_stability
    (h : ModularCorePublishedInputs.{u})
    (hModular : PublishedModularSpectralResolution.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIII1Factor M → TypeIII1Factor N →
      ExpectedMatrixSubfactorModel M → ExpectedMatrixSubfactorModel N →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
        MatrixNearInclusion M N γ → MatrixNearInclusion N M γ → NearConjugacy M N ε := by
  obtain ⟨δ, hδ, hstable⟩ := uniform_expected_matrix_typeIII1_stability
    h hModular hε
  refine ⟨δ, hδ, ?_⟩
  intro H _ _ _ _ _ M N hM hN E F γ hγ hsmall hgap hMN hNM
  exact hstable H M N hM hN E.stage E.increasing E.trace E.expectation E.unital
    E.left_module E.right_module E.vector E.vector_state E.cyclic E.separating E.irreducible
    F.vector F.unit_vector F.cyclic F.separating γ hγ hsmall hgap hMN hNM

end

end KadisonKastler

end OAI
