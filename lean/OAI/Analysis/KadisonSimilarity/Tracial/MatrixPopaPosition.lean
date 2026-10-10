import OAI.Analysis.KadisonSimilarity.Tracial.MatrixDiagonalEmbedding
import OAI.Analysis.KadisonSimilarity.Tracial.PopaConjugatePosition

namespace OAI

/-! The fixed source factor is conjugated diagonally inside the prescribed
matrix-subfactor ultrapower. Trace and inclusion properties follow from the
concrete maps, with no operator-estimate hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (n : ℕ) [NeZero n]

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ρn" => matrixEntryHom (n := n) ρ
local notation "hρn" => normalizedMatrixTrace_entryHom τR τB ρ hρτ

/-- The conjugate of the fixed source factor, diagonal in the matrix
subfactor before passing to the tracial ultrapower. -/
def matrixConjugatedEmbedding (u : unitary (Ultrapower τRn hRn ω trRn)) :
    R →⋆ₐ[ℂ] Ultrapower τBn hBn ω trBn :=
  conjugatedConstantEmbedding τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) u

theorem matrixConjugatedEmbedding_trace
    (u : unitary (Ultrapower τRn hRn ω trRn)) (a : R) :
    quotientTrace τBn hBn ω trBn
      (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u a) = τR a := by
  change quotientTrace τBn hBn ω trBn
    (conjugatedConstantEmbedding τRn τBn hRn hBn ω trRn trBn ρn hρn
      (matrixDiagonalHom n) u a) = τR a
  rw [conjugatedConstantEmbedding_trace, normalizedMatrixTrace_diagonal]

theorem matrixConjugatedEmbedding_injective
    (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
    (u : unitary (Ultrapower τRn hRn ω trRn)) :
    Function.Injective (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u) :=
  conjugatedConstantEmbedding_injective τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) (matrixDiagonalHom_injective n)
    (normalizedMatrixTrace_faithful τR hfR) u

theorem matrixConjugatedEmbedding_range_le
    (u : unitary (Ultrapower τRn hRn ω trRn)) :
    (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u).range ≤
      (tracialUltrapowerMap τRn τBn hRn hBn ω trRn trBn ρn hρn).range :=
  conjugatedConstantEmbedding_range_le τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) u

end KadisonSimilarity

end

end OAI
