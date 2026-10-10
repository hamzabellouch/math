import OAI.Analysis.KadisonKastler.Amenable
import OAI.Analysis.KadisonKastler.IrreducibleMatrixSubfactor

namespace OAI

/-! # Injectivity of the increasing matrix construction

The input retains only approximately finite-dimensional implies injective.
An explicit primary statement is Connes, *Von Neumann algebras*, Proceedings
ICM (Helsinki, 1978), Acad. Sci. Fennica (1980), 97--109: p. 105 gives the
norm-one projection definition and closure under ascending weakly closed
unions, and p. 106 displays AFD implies property P implies injectivity.

Primary published volume:
https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1978.1/ICM1978.1.ocr.pdf

The stage sequence and irreducibility are constructed in the existing
formalization. Only the ambient contractive projection is retained as a
published input; the reverse classification implication is not used.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The AFD-to-injective implication specialized to the actual increasing
full-matrix stages used in the irreducible subfactor construction. -/
def PublishedIncreasingMatrixInjectivity : Prop :=
  ∀ (M : VonNeumannAlgebra H) (A : ℕ → FiniteMatrixStage M),
    Monotone (fun n => (A n).units.concreteAlgebra) →
    (∀ n, FiniteDimensional ℂ (A n).units.concreteAlgebra) →
    IsInjective (FiniteMatrixStage.generatedVonNeumann A)

/-- The constructed irreducible matrix-generated subfactor is injective
conditionally only on the indicated published AFD implication. -/
theorem exists_irreducible_injective_subfactor
    (hpub : PublishedIncreasingMatrixInjectivity (H := H))
    {M : VonNeumannAlgebra H} (τ : UltrapowerBridge.TracialRepresentation M)
    (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ (R : VonNeumannAlgebra H) (hRM : R ≤ M),
      IsII1Factor R.toStarSubalgebra ∧ IsInjective R ∧
      (∀ b : Algebra M,
        (∀ r : Algebra R, coordinateInclusion hRM r * b = b * coordinateInclusion hRM r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  obtain ⟨R, hRM, hR, hirr, A, hRA, hmono, hfd⟩ :=
    exists_irreducible_matrix_subfactor τ hM
  refine ⟨R, hRM, hR, ?_, hirr⟩
  rw [hRA]
  exact hpub M A hmono hfd

end

end KadisonKastler

end OAI
