import OAI.Analysis.KadisonKastler.StandardTypeIIIVector
import OAI.Analysis.KadisonKastler.ExpectedFromRefinement
import OAI.Analysis.KadisonKastler.CentralContractionIteration

namespace OAI

/-! # Expected matrix subfactors from a uniform central-vector contraction

A strict contraction on the orthogonal residual, with arbitrarily
small displacement of the projected reference vector, gives the
expected matrix subfactor by iteration and passage to a strong limit.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_central_contraction
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖ = 1)
    (d : ModularConjugationData M ξ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      inner ℂ η (matrixStageCentralProjection E d.conjugation ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E d.conjugation ξ -
          matrixStageCentralProjection F d.conjugation ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F d.conjugation η‖ ≤ q * ‖η‖) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  exact expectedMatrixSubfactorModel_of_local_refinement hM d.conjugation d.involutive
    (d.right_mem le_rfl) d.left_mem ξ hunit d.fixes_vector
    (exists_central_refinement_of_contraction d.conjugation ξ q hq hq1 hstep)

end

end KadisonKastler

end OAI
