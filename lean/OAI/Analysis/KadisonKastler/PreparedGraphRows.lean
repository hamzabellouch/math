import OAI.Analysis.KadisonKastler.PreparedGraphComparison

namespace OAI

/-! # Prepared graph comparison from individual row approximants

Only a separate nearby row is required for each finite row in either
algebra. No global linear map selecting those approximants is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedGraphRowsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedGraphRowsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedGraphRowsOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance preparedGraphRowsOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The individual finite-row approximation property used in the graph
construction. This notation imposes no compatibility among the choices. -/
abbrev GraphRowApproximation (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∀ (k : ℕ) (X : Fin k → H →L[ℂ] H), (∀ i, X i ∈ M) →
    ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
      ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖

/-- Common matrix actions and two-sided individual row approximation
imply the uniform comparison of every positively rescaled closed graph. -/
theorem norm_prepared_rescaledGraphProjection_sub_le_of_row_approx
    (M N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hEN : ∀ n, (E n).algebra ≤ N.toStarSubalgebra)
    (hirrM : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hirrN : ∀ A ∈ N, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentralM : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (hcentralN : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ N,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : GraphRowApproximation M N γ) (hNM : GraphRowApproximation N M γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  have hb : 0 ≤ (16 * Real.sqrt 2 * 131072) * γ := by positivity
  have hMN : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤
        (16 * Real.sqrt 2 * 131072) * γ := by
    intro c hc
    exact norm_graphProjectionDefect_le_of_row_approx_scale M N Ω hΩ d E hmono hEM
      hirrM hcentralM J hJ hcommM hcommN hEN hvector hc hγ
      hMN
  have hNM : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection M J Ω c) * rescaledGraphProjection N J Ω c‖ ≤
        (16 * Real.sqrt 2 * 131072) * γ := by
    intro c hc
    exact norm_graphProjectionDefect_le_of_row_approx_scale N M Ω hΩ d E hmono hEN
      hirrN hcentralN J hJ hcommN hcommM hEM hvector hc hγ
      hNM
  have h := uniform_rescaledGraphProjection_comparison M N J hJ Ω hb hMN hNM hc
  convert h using 1
  ring

end

end KadisonKastler

end OAI
