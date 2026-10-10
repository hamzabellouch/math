import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange
import OAI.Analysis.KadisonSimilarity.Tracial.TracialInputTransport

namespace OAI

/-! Spectral rounding for finite matrices in an actual normal representation. -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Any faithful normal realization supplies all finite-matrix rounding
inputs, for every positive functional on the matrix algebra. -/
theorem matrix_spectralProjectionRoundingInput_of_concrete_range
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hσ : Function.Injective σ)
    (P : VonNeumannAlgebra H) (hrange : σ.range = P.toStarSubalgebra)
    (n : ℕ) [NeZero n] (τ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_concrete_range (matrixVonNeumann P n) τ
    (representedMatrixHom σ n) (representedMatrixHom_injective σ hσ n)
    (representedMatrixHom_range σ P hrange n)


end KadisonSimilarity

end

end OAI
