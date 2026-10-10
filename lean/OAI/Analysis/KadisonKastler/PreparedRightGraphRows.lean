import OAI.Analysis.KadisonKastler.PreparedGraphRows
import OAI.Analysis.KadisonKastler.IncreasingMatrixPreparation

namespace OAI

/-! # Prepared right actions with individual row approximants

The finite matrix and common right-action arguments do not require a
linear choice of nearby operators. These variants retain only the actual
finite-row approximations supplied by matrix unit-ball proximity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedRightRowsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightRowsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedRightRowsOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightRowsOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Common right-action identities give all graph comparison hypotheses;
individual row approximants suffice for the remaining analytic step. -/
theorem norm_preparedRight_graphProjection_sub_le_of_row_approx
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hrightN : ∀ r ∈ R, conjugationOperator J r ∈ N.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : GraphRowApproximation M N γ) (hNM : GraphRowApproximation N M γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  have hER (n : ℕ) : (E n).algebra ≤ R.toStarSubalgebra := by
    intro a ha
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun n => (E n).algebra) n) ha)
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra :=
    fun _ ha => hRM (hER n ha)
  have hEN (n : ℕ) : (E n).algebra ≤ N.toStarSubalgebra :=
    fun _ ha => hRN (hER n ha)
  have hirrM : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAM hA
    apply hirr A hAM
    rw [hR]
    exact commute_generated_of_commute_matrix_stages d E A hA
  have hirrNg := relative_irreducibility_of_near_increasing_matrices M N d E hmono hEM
    (by simpa only [← hR] using hirr) hgap
  have hirrN : ∀ A ∈ N, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAN hA
    exact hirrNg A hAN (commute_generated_of_commute_matrix_stages d E A hA)
  have hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant := by
    intro j a ha
    exact hrightM (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant := by
    intro j a ha
    exact hrightN (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hvectorE : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω := by
    intro j a ha
    exact hvector a (hER j ha)
  have hcentralM : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R M hRM J hJ Ω hrightM hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  have hcentralN : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ N,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R N hRN J hJ Ω hrightN hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  exact norm_prepared_rescaledGraphProjection_sub_le_of_row_approx M N Ω hΩ d E hmono
    hEM hEN hirrM hirrN hcentralM hcentralN J hJ hcommM hcommN hvectorE
    hγ hMN hNM hc

/-- The localized right correction is independent of the row approximants.
After choosing it, every pair of row bounds gives the graph estimate. -/
theorem exists_preparedRight_row_graph_comparison
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N) (hRinj : IsInjective R)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    {ρ : ℝ} (hnear : NearInclusion (conjugateRightAlgebra J hJ R) N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra J hJ R ≤ (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ γ : ℝ, 0 ≤ γ →
        GraphRowApproximation M (unitaryConjugateAlgebra (star w) N) γ →
        GraphRowApproximation (unitaryConjugateAlgebra (star w) N) M γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M J Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  let S := conjugateRightAlgebra J hJ R
  have hSR : S ≤ R.commutant := commonRightAlgebra_le_commutant M R S hRM J
    hrightM (conjugateRightAlgebra_coe J hJ R)
  obtain ⟨w, hleft, hright, hnorm, hdist⟩ := exists_prepared_right_correction hpub
    M N R S hRN hSR (isInjective_conjugateRightAlgebra J hJ R hRinj) hnear hρ
  refine ⟨w, hleft, hright, hnorm, hdist, ?_⟩
  intro γ hγ hMN hNM c hc
  apply norm_preparedRight_graphProjection_sub_le_of_row_approx M
    (unitaryConjugateAlgebra (star w) N) R J hJ Ω hΩ d E hmono hR hRM hleft hirr
    (hdist.trans_lt hgap) hrightM ?_ hvector hγ hMN hNM hc
  intro r hr
  exact hright ⟨r, hr, rfl⟩

/-- The increasing-matrix injectivity input supplies both injectivity
requirements in the row version of preparation. -/
theorem exists_prepared_matrixStage_row_graph_comparison
    (hAFD : PublishedIncreasingMatrixInjectivity (H := H))
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N : VonNeumannAlgebra H) (A : ℕ → Generator.FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hRN : Generator.FiniteMatrixStage.generatedVonNeumann A ≤ N)
    (hirr : ∀ T ∈ M,
      (∀ r ∈ Generator.FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ Generator.FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ Generator.FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator J (star r) Ω = r Ω)
    {ρ : ℝ} (hnear : NearInclusion
      (conjugateRightAlgebra J hJ (Generator.FiniteMatrixStage.generatedVonNeumann A))
      N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      Generator.FiniteMatrixStage.generatedVonNeumann A ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra J hJ (Generator.FiniteMatrixStage.generatedVonNeumann A) ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ γ : ℝ, 0 ≤ γ →
        GraphRowApproximation M (unitaryConjugateAlgebra (star w) N) γ →
        GraphRowApproximation (unitaryConjugateAlgebra (star w) N) M γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M J Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  exact exists_preparedRight_row_graph_comparison hpub M N
    (Generator.FiniteMatrixStage.generatedVonNeumann A) J hJ Ω hΩ
    (fun n => (A n).size) (matrixStageConcreteUnits A)
    (by simpa only [matrixStageConcreteUnits_algebra] using hA)
    (generated_matrixStages_eq A hA) (Generator.FiniteMatrixStage.generatedVonNeumann_le A) hRN
    (hAFD M A hA (fun n => (A n).units.concrete_finiteDimensional))
    hirr hrightM hvector hnear hρ hgap

end

end KadisonKastler

end OAI
