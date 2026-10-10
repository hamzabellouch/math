import OAI.Analysis.KadisonKastler.ExpectedModularPreparation
import OAI.Analysis.KadisonKastler.PreparedRightGraphRows
import OAI.Analysis.KadisonKastler.VectorStateTracialRepresentation

namespace OAI

/-! # Expected modular preparation with individual row approximants

The expected-state construction supplies all common right-action data.
Only separate finite-row approximants are used in the graph comparison.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance expectedModularRowsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularRowsStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
local instance expectedModularRowsOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularRowsOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- An expectation onto the finite common algebra supplies the right data;
no global choice of a nearby operator is required. -/
theorem exists_expected_modular_row_graph_comparison
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRinj : IsInjective R)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {ρ : ℝ}
    (hnear : NearInclusion (conjugateRightAlgebra d.conjugation d.involutive R)
      N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra d.conjugation d.involutive R ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ γ : ℝ, 0 ≤ γ →
        GraphRowApproximation M (unitaryConjugateAlgebra (star w) N) γ →
        GraphRowApproximation (unitaryConjugateAlgebra (star w) N) M γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M d.conjugation Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) d.conjugation Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  obtain ⟨hnorm, hmem, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  exact exists_preparedRight_row_graph_comparison hpub M N R
    d.conjugation d.involutive Ω hnorm s E hmono hR hRM hRN hRinj hirr
    hmem hvector hnear hρ hgap

/-- Actual increasing matrix stages supply injectivity. The expectation
and modular conjugation supply the central vector and common right action. -/
theorem exists_expected_matrixStage_row_graph_comparison
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N : VonNeumannAlgebra H) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann A)))
    (P : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann A))
    (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
      P (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * x) =
        r * P x)
    (hright : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
      P (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) =
        P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (hRN : FiniteMatrixStage.generatedVonNeumann A ≤ N)
    (hirr : ∀ T ∈ M,
      (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {ρ : ℝ} (hnear : NearInclusion
      (conjugateRightAlgebra d.conjugation d.involutive
        (FiniteMatrixStage.generatedVonNeumann A)) N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      FiniteMatrixStage.generatedVonNeumann A ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra d.conjugation d.involutive (FiniteMatrixStage.generatedVonNeumann A) ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ γ : ℝ, 0 ≤ γ →
        GraphRowApproximation M (unitaryConjugateAlgebra (star w) N) γ →
        GraphRowApproximation (unitaryConjugateAlgebra (star w) N) M γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M d.conjugation Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) d.conjugation Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  exact exists_expected_modular_row_graph_comparison hpub M N
    (FiniteMatrixStage.generatedVonNeumann A) (FiniteMatrixStage.generatedVonNeumann_le A)
    hRN τ P hP hleft hright Ω hΩ d (fun n => (A n).size) (matrixStageConcreteUnits A)
    (by simpa only [matrixStageConcreteUnits_algebra] using hA)
    (generated_matrixStages_eq A hA)
    (isInjective_matrix_closure_of_generated_vector_state A hA τ Ω
      (trace_vector_of_expected_state (FiniteMatrixStage.generatedVonNeumann_le A)
        τ P hP hleft Ω hΩ))
    hirr hnear hρ hgap

end

end KadisonKastler

end OAI
