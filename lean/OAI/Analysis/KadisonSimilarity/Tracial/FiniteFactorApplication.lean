import OAI.Analysis.KadisonSimilarity.Representation.FiniteStandardEstimate
import OAI.Analysis.KadisonSimilarity.FreeProduct.MatrixFreeCornerApplication
import OAI.Analysis.KadisonSimilarity.Tracial.TracialStageCommutation
import OAI.Analysis.KadisonSimilarity.Representation.NormalRepresentationReduction
import OAI.Analysis.KadisonSimilarity.Tracial.TracialFactorComparison
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixTracialInputTransport
import OAI.Analysis.KadisonSimilarity.Tracial.NormalSmallCorners

namespace OAI

/-! # Finite-factor application of the free-corner argument

The local hypotheses below specify the actual increasing-matrix inclusion,
its normal represented closure, and the published projection and free-product
inputs. The commutator estimates combine Haar averaging, the free-corner
theorem, and the exact
finite and countable amplification transfers.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

variable (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

/-- Exact remaining structural inputs for the fixed finite-factor application.
Only the free position remains explicit. Stage commutation, source and
generated-factor comparison, rounding and diffuse corners are constructed
from the faithful normal traces and the dense matrix tower. -/
structure FiniteFactorFreeCornerInputs : Prop where
  free_position : ∀ (n : ℕ) [NeZero n],
    Popa1995ConjugateFreenessInput
      (normalizedMatrixTrace τR n) (normalizedMatrixTrace τB n)
      (normalizedMatrixTrace_one τR hR) (normalizedMatrixTrace_one τB hB)
      ω (normalizedMatrixTrace_tracial τR trR) (normalizedMatrixTrace_tracial τB trB)
      (matrixEntryHom ρ) (normalizedMatrixTrace_entryHom τR τB ρ hρτ)
      hω (matrixDiagonalHom n)

include hfR hfB M in
/-- The paper's finite-standard-multiplicity estimate. The centered test is
proved from the local free-corner theorem after extending stage commutation
by the actual trace-vector density. -/
theorem finite_standard_bound_of_local_free_corner
    (inputs : FiniteFactorFreeCornerInputs τR τB hR hB ω trR trB ρ hρτ hω)
    (source_normalR : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {r : ℕ} (Y : HilbertCopies τB.GNS r →L[ℂ] HilbertCopies τB.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τB.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) B) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τB.gnsStarAlgHom r) X)‖ ≤
      (3 * cornerConstant + 2) * δ * ‖X‖ := by
  apply finite_standard_estimate_of_centered_tests τB
    (fun j => ρ.comp (M.embedding j)) M.inclusion
    (fun j k h a => congrArg ρ (M.compatible j k h a))
    (le_of_lt cornerConstant_pos) _ Y hδ hscalar h X
  intro m _ Y₀ ε hε hscalar₀ hstage x hxstar hxsq hx0
  have hm : 0 < m := NeZero.pos m
  obtain ⟨Q⟩ := (gnsTracialGeometry τR trR).exists_smallFreeCornerData_of_normal_matrix_tower
    M hR (gnsTracialVector_injective τR hfR) _ source_normalR hsize
    (show 0 < ((4 * m : ℕ) : ℝ)⁻¹ by positivity)
  have hcomm (a : R) :
      Y₀.comp (amplify (τB.gnsStarAlgHom (ρ a)) (4 * m)) =
        (amplify (τB.gnsStarAlgHom (ρ a)) (4 * m)).comp Y₀ := by
    exact commutes_amplified_source_of_matrix_stages τR τB hB trB hfB source_normal
      ρ hρτ M (4 * m) Y₀ hstage a
  exact matrix_symmetry_bound_of_local_free_corner τR τB hR hB ω trR trB
    ρ hρτ hfR hfB (4 * m) M Q hω (inputs.free_position (4 * m)) S hsize
    (matrix_projectionComparison_of_tower τR hR trR hfR M source_normalR (4 * m))
    (matrix_spectralProjectionRoundingInput_of_concrete_range τR.gnsStarAlgHom
      ((gnsTracialGeometry τR trR).left_injective (gnsTracialVector_injective τR hfR))
      _ source_normalR (4 * m) _) source_normal
    (fun u hfree x _ hxsq =>
      matrixFreeCornerLocalInput_of_normal_source τR τB hR hB ω trR trB
        ρ hρτ hfR hfB (4 * m) M Q hω source_normalR hsize u hfree x hxsq) Y₀ hcomm (by positivity) hscalar₀ x hxstar hxsq hx0

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

include hfR hfB M in
/-- The same finite-factor bound in an arbitrary supplied normal
representation, with no increase of the finite-standard constant. -/
theorem normal_bound_of_local_free_corner
    (inputs : FiniteFactorFreeCornerInputs τR τB hR hB ω trR trB ρ hρτ hω)
    (source_normalR : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (embedding : HiaiNormalStandardEmbeddingInput τB σ)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) B) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤
      (3 * cornerConstant + 2) * δ * ‖X‖ := by
  apply normal_representation_bound_of_finite τB σ embedding
    (by have := cornerConstant_pos; positivity) _ Y hδ hscalar n X
  intro r T ε hε hbound m Z
  exact finite_standard_bound_of_local_free_corner τR τB hR hB ω trR trB
    ρ hρτ hfR hfB M hω inputs source_normalR source_normal S hsize T hε hbound m Z

end KadisonSimilarity

end

end OAI
