import OAI.Analysis.KadisonSimilarity.FreeProduct.CanonicalFreeCornerEstimate
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixPopaPosition
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixGNSNormality

namespace OAI

/-! # The free-corner estimate for an actual matrix GNS operator

The matrix subfactor is the entrywise image of the original inclusion.
Projection comparison transports the scalar bound to all sufficiently small
matrix corners. Popa's local conjugacy input chooses the free copy, while
all native GNS geometry is the canonical generated geometry. The remaining
local input consists exactly of the published structural data for that
geometry; it contains no commutator bound.
-/

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
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (n : ℕ) [NeZero n]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (Q : SmallFreeCornerData τR.toLinearMap (n : ℝ)⁻¹)

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ρn" => matrixEntryHom (n := n) ρ
local notation "hρn" => normalizedMatrixTrace_entryHom τR τB ρ hρτ
local notation "ψ" => matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n
local notation "hψτ" => matrixConjugatedEmbedding_trace τR τB hR hB ω trR trB ρ hρτ n
local notation "hψ" => matrixConjugatedEmbedding_injective τR τB hR hB ω trR trB ρ hρτ n hfR

/-- The exact local published bundle on the canonical matrix free-product
model. This abbreviation only fixes the generated geometry and transported
frame; it does not assert the existence of any of its fields. -/
abbrev MatrixFreeCornerLocalInput
    (u : unitary (Ultrapower τRn hRn ω trRn))
    (x : CStarMatrix (Fin n) (Fin n) B) (hxsq : x * x = 1) : Prop :=
  CanonicalFreeCornerInput τBn τR hBn ω trBn (ψ u) (hψτ u)
    (hψ u) M
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q)
    x hxsq

include hfB in
/-- Construct the actual matrix free-product comparison from the normal
source and its matrix tower. -/
theorem matrixFreeCornerLocalInput_of_normal_source
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hsource : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (u : unitary (Ultrapower τRn hRn ω trRn))
    (hf : ScalarFree (quotientTrace τBn hBn ω trBn).toLinearMap
      (constant τBn hBn ω trBn).range (ψ u).range)
    (x : CStarMatrix (Fin n) (Fin n) B) (hxsq : x * x = 1) :
    MatrixFreeCornerLocalInput τR τB hR hB ω trR trB ρ hρτ hfR n M Q u x hxsq :=
  canonicalFreeCornerInput_of_normal_source τBn τR hBn ω trBn (ψ u) (hψτ u)
    (normalizedMatrixTrace_faithful τB hfB) (hψ u) M hω hf hsource hsize
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q) x hxsq

include hfB in
/-- The matrix GNS centered-symmetry estimate, derived from projection
comparison, the free-position input and the structural local bundles. -/
theorem matrix_symmetry_bound_of_local_free_corner
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (popa : Popa1995ConjugateFreenessInput τRn τBn hRn hBn ω trRn trBn
      ρn hρn hω (matrixDiagonalHom n))
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (comparison : FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) R => (τRn X).re))
    (rounding : SpectralProjectionRoundingInput τRn)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (published : ∀ (u : unitary (Ultrapower τRn hRn ω trRn)),
      ScalarFree (quotientTrace τBn hBn ω trBn).toLinearMap
        (constant τBn hBn ω trBn).range (ψ u).range →
      ∀ (x : CStarMatrix (Fin n) (Fin n) B), star x = x → ∀ hxsq : x * x = 1,
        MatrixFreeCornerLocalInput τR τB hR hB ω trR trB ρ hρτ hfR n M Q u x hxsq)
    (Y₀ : HilbertCopies τB.GNS n →L[ℂ] HilbertCopies τB.GNS n)
    (hcomm : ∀ a : R, Y₀.comp (amplify (τB.gnsStarAlgHom (ρ a)) n) =
      (amplify (τB.gnsStarAlgHom (ρ a)) n).comp Y₀)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hscalar : ∀ a : B, ‖commutator Y₀ (amplify (τB.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (x : CStarMatrix (Fin n) (Fin n) B)
    (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τBn x = 0) :
    ‖commutator (matrixGNSLiftOperator τB Y₀) ((τBn).gnsStarAlgHom x)‖ ≤
      cornerConstant * ε := by
  obtain ⟨u, hfree⟩ := popa
  have hD := matrixConjugatedEmbedding_range_le τR τB hR hB ω trR trB ρ hρτ n u
  have hcorner := matrix_gns_all_small_corners ρ τB τR hR comparison Y₀ hcomm hε hscalar
  exact original_symmetry_bound_of_free_corner τRn τBn τR hRn hBn ω trRn trBn
    ρn hρn (ψ u) (hψτ u) (normalizedMatrixTrace_faithful τB hfB) (hψ u) M
    hω hD hfree S hsize
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q)
    x hxstar hxsq hx0
    (matrix_trace_balls_closed τB _ source_normal n hB trB hfB)
    (published u hfree x hxstar hxsq) rounding
    (matrixGNSLiftOperator τB Y₀)
    (fun a => matrix_gns_commutes_subfactor ρ τB Y₀ hcomm a)
    hε hcorner

end KadisonSimilarity

end

end OAI
