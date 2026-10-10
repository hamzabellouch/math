import OAI.Analysis.KadisonKastler.ExpectedFromCentralTests
import OAI.Analysis.KadisonKastler.CentralRefinementSequence
import OAI.Analysis.KadisonKastler.MatrixCentralVectorTests

namespace OAI

/-! # The expected-subfactor construction from one-vector refinement

This is the closing construction in Haagerup's Lemma 3.8: finite tests,
a summable increasing sequence, the central line, and the support corner.
The local one-vector refinement hypothesis is kept explicit here; proving
it from the absorbing type III₁ hypotheses remains a separate step.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem scalarStage_centralProjection (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) :
    matrixStageCentralProjection (FiniteMatrixStage.scalarStage M) J ξ = ξ := by
  apply Submodule.starProjection_eq_self_iff.mpr
  apply (mem_centralVectorSpace_matrix_iff _ J ξ).mpr
  intro i j
  change ξ = conjugationOperator J (star (1 : H →L[ℂ] H)) ξ
  rw [star_one,conjugationOperator_one J hJ]
  rfl

theorem expectedMatrixSubfactorModel_of_local_refinement
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  obtain ⟨η,hdense⟩ := TopologicalSpace.exists_dense_seq (α := H)
  obtain ⟨A,hA,hdisp,htest⟩ := exists_central_refinement_sequence J ξ hstep
    (FiniteMatrixStage.scalarStage M) (scalarStage_centralProjection J hJ ξ) η (1 / 2)
    (by norm_num)
  exact expectedMatrixSubfactorModel_of_central_tests hM A hA J hJ hleft hright ξ hunit hJξ
    η hdense (correctionScale 1) (correctionScale_tendsto 1) (1 / 2) (by norm_num) hdisp htest

end

end KadisonKastler

end OAI
