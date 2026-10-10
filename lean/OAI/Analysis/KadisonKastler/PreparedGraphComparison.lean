import OAI.Analysis.KadisonKastler.GraphRowApproximation

namespace OAI

/-! # Uniform graph comparison in a prepared pair

The genuine matrix averages and the two completely close linear maps
supply every hypothesis of the row construction. The final estimate is
uniform over all positive rescalings of the two closed Tomita graphs.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedGraphOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedGraphStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedGraphOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance preparedGraphOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual common matrix actions and complete map bounds imply uniform
comparison of every positively rescaled closed graph. -/
theorem norm_prepared_rescaledGraphProjection_sub_le
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
    (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H)) (G : Algebra N →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) (hGM : ∀ x, G x ∈ M) {γ : ℝ} (hγ : 0 ≤ γ)
    (hF : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (hG : CompletelyBoundedBy (N.toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ)
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
      (exists_graphRow_approx_of_completelyBoundedBy M N F hFN hF)
  have hNM : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection M J Ω c) * rescaledGraphProjection N J Ω c‖ ≤
        (16 * Real.sqrt 2 * 131072) * γ := by
    intro c hc
    exact norm_graphProjectionDefect_le_of_row_approx_scale N M Ω hΩ d E hmono hEN
      hirrN hcentralN J hJ hcommN hcommM hEM hvector hc hγ
      (exists_graphRow_approx_of_completelyBoundedBy N M G hGM hG)
  have h := uniform_rescaledGraphProjection_comparison M N J hJ Ω hb hMN hNM hc
  convert h using 1
  ring

end

end KadisonKastler

end OAI
