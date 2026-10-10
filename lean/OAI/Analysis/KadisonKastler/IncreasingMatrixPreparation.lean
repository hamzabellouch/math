import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra
import OAI.Analysis.KadisonKastler.PublishedIncreasingMatrixInjectivity

namespace OAI

/-! # Increasing full matrix stages in the preparation argument

The finite-stage construction and the graph comparison use two equivalent
presentations of the same concrete matrix algebras. Their generated
von Neumann algebras agree, so approximate finite dimensionality gives
injectivity on both sides of the prepared graph.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- The ambient matrix units of a finite stage. -/
def matrixStageConcreteUnits (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    MatrixUnitSystem (Fin (A n).size) (H →L[ℂ] H) :=
  (A n).units.map M.toStarSubalgebra.subtype

theorem matrixStageConcreteUnits_algebra (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    (matrixStageConcreteUnits A n).algebra = (A n).units.concreteAlgebra := by
  have he : (matrixStageConcreteUnits A n).hom = (A n).units.concreteHom := by
    ext a
    simp only [matrixStageConcreteUnits, MatrixUnitSystem.hom_apply,
      MatrixUnitSystem.map_entry, MatrixUnitSystem.concreteHom,
      StarAlgHom.comp_apply, map_sum, map_smul]
  change (matrixStageConcreteUnits A n).hom.range = (A n).units.concreteHom.range
  rw [he]

/-- The two actual closure constructions agree. -/
theorem generated_matrixStages_eq (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    FiniteMatrixStage.generatedVonNeumann A =
      generatedVonNeumannAlgebra (⨆ n, (matrixStageConcreteUnits A n).algebra) := by
  have he : (⨆ n, (matrixStageConcreteUnits A n).algebra) =
      FiniteMatrixStage.stageUnion A := by
    simp only [matrixStageConcreteUnits_algebra, FiniteMatrixStage.stageUnion]
  rw [he]
  apply SetLike.coe_injective
  change (FiniteMatrixStage.generated A : Set (H →L[ℂ] H)) =
    (generatedVonNeumannAlgebra (FiniteMatrixStage.stageUnion A) : Set (H →L[ℂ] H))
  rw [FiniteMatrixStage.generated_eq_wstar_union A hA,
    wstar_starAlgebra_eq_bicommutant]
  change (bicommutantVonNeumann (FiniteMatrixStage.stageUnion A) : Set (H →L[ℂ] H)) = _
  rw [bicommutantVonNeumann_coe, generatedVonNeumannAlgebra_coe]

/-- The published increasing-matrix input applies directly to the matrix
stages that enter the graph argument. -/
theorem isInjective_generated_matrixStages
    (hAFD : PublishedIncreasingMatrixInjectivity (H := H))
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (generatedVonNeumannAlgebra (⨆ n, (matrixStageConcreteUnits A n).algebra)) := by
  rw [← generated_matrixStages_eq A hA]
  exact hAFD M A hA (fun n => (A n).units.concrete_finiteDimensional)

local instance matrixStageGraphOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance matrixStageGraphStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixStageGraphOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixStageGraphOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual increasing finite matrix stages supply both injectivity inputs
in the generic preparation-to-graph theorem. -/
theorem exists_prepared_matrixStage_graph_comparison
    (hAFD : PublishedIncreasingMatrixInjectivity (H := H))
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (N : VonNeumannAlgebra H) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hRN : FiniteMatrixStage.generatedVonNeumann A ≤ N)
    (hirr : ∀ T ∈ M,
      (∀ a ∈ FiniteMatrixStage.generatedVonNeumann A, a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator J (star r) Ω = r Ω)
    {ρ : ℝ} (hnear : NearInclusion
      (conjugateRightAlgebra J hJ (FiniteMatrixStage.generatedVonNeumann A)) N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      FiniteMatrixStage.generatedVonNeumann A ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra J hJ (FiniteMatrixStage.generatedVonNeumann A) ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
        (G : Algebra (unitaryConjugateAlgebra (star w) N) →ₗ[ℂ] (H →L[ℂ] H))
        (γ : ℝ),
        (∀ x, F x ∈ unitaryConjugateAlgebra (star w) N) → (∀ x, G x ∈ M) →
        0 ≤ γ →
        CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ →
        CompletelyBoundedBy
          ((unitaryConjugateAlgebra (star w) N).toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M J Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  exact exists_preparedRight_graph_comparison_of_injective hpub M N
    (FiniteMatrixStage.generatedVonNeumann A) J hJ Ω hΩ
    (fun n => (A n).size) (matrixStageConcreteUnits A)
    (by simpa only [matrixStageConcreteUnits_algebra] using hA)
    (generated_matrixStages_eq A hA) (FiniteMatrixStage.generatedVonNeumann_le A) hRN
    (hAFD M A hA (fun n => (A n).units.concrete_finiteDimensional))
    hirr hrightM hvector hnear hρ hgap

end

end KadisonKastler

end OAI
