import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorApplication
import OAI.Analysis.KadisonSimilarity.Representation.FiniteTypeIEstimate
import OAI.Analysis.KadisonSimilarity.Representation.ProperlyInfiniteEstimate
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteGNSNormality
import OAI.Analysis.KadisonSimilarity.Tracial.NormalRealSequence
import OAI.Analysis.KadisonSimilarity.Representation.NormalStandardEmbedding

namespace OAI

/-! # The three factor branches

The finite branch records only the fixed trace, matrix presentation, and
local published inputs used in the preceding application. The alternatives
are the structural factor classification; no alternative assumes an
operator estimate. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (P : VonNeumannAlgebra H) :
    IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

/-- The complete finite-factor presentation required for the application. -/
structure FiniteFactorModel (P : VonNeumannAlgebra H) where
  R : Type u
  [cstar : CStarAlgebra R]
  [order : PartialOrder R]
  [starOrder : StarOrderedRing R]
  traceR : R →ₚ[ℂ] ℂ
  traceP : P.toStarSubalgebra →ₚ[ℂ] ℂ
  oneR : traceR 1 = 1
  oneP : traceP 1 = 1
  tracialR : ∀ a b, traceR (a * b) = traceR (b * a)
  tracialP : ∀ a b, traceP (a * b) = traceP (b * a)
  faithfulR : ∀ a, traceR (star a * a) = 0 → a = 0
  /-- Normality of the chosen source trace in its native GNS model. -/
  normalR : HasNormalGNS traceR
  faithfulP : ∀ a, traceP (star a * a) = 0 → a = 0
  /-- Normality of the chosen finite trace, in its native faithful GNS model. -/
  normalP : HasNormalGNS traceP
  inclusion : R →⋆ₐ[ℂ] P.toStarSubalgebra
  trace_inclusion : ∀ a, traceP (inclusion a) = traceR a
  size : ℕ → ℕ
  [stageNonempty : ∀ j, Nonempty (Fin (size j))]
  matrices : NestedTracialMatrices (A := fun j => Fin (size j))
    traceR.toLinearMap (gnsTracialVector traceR)
  size_tendsto : Filter.Tendsto (fun j => (Fintype.card (Fin (size j)) : ℝ))
    Filter.atTop Filter.atTop
  omega : Ultrafilter ℕ
  omega_cofinite : (omega : Filter ℕ) ≤ Filter.cofinite
  localInputs : FiniteFactorFreeCornerInputs traceR traceP oneR oneP omega
    tracialR tracialP inclusion trace_inclusion omega_cofinite

attribute [instance] FiniteFactorModel.cstar FiniteFactorModel.order
  FiniteFactorModel.starOrder FiniteFactorModel.stageNonempty

/-- Every finite presentation gives the concrete represented estimate. -/
theorem FiniteFactorModel.estimate [TopologicalSpace.SeparableSpace H]
    {P : VonNeumannAlgebra H} (F : FiniteFactorModel P) :
    CommutatorEstimate P (3 * cornerConstant + 2) := by
  obtain ⟨S⟩ := (gnsTracialGeometry F.traceR F.tracialR).exists_realTracialSequence_of_normal_matrix_tower
    F.matrices F.oneR (gnsTracialVector_injective F.traceR F.faithfulR) _ F.normalR F.size_tendsto
  apply normal_factor_commutatorEstimate_of_finite P F.traceP
    (normal_standard_embedding_of_normal_gns P F.traceP F.oneP F.tracialP
      F.faithfulP F.normalP)
    (by have := cornerConstant_pos; positivity)
  intro r T δ hδ hscalar n X
  exact finite_standard_bound_of_local_free_corner F.traceR F.traceP F.oneR F.oneP
    F.omega F.tracialR F.tracialP F.inclusion F.trace_inclusion F.faithfulR F.faithfulP
    F.matrices F.omega_cofinite F.localInputs
    F.normalR F.normalP
    S F.size_tendsto T hδ hscalar n X

/-- The structural data of a finite type-I factor in its given representation. -/
structure FiniteMatrixFactorModel (P : VonNeumannAlgebra H) where
  size : ℕ
  size_ne_zero : size ≠ 0
  inclusion : Matrix (Fin size) (Fin size) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)
  mem : ∀ a, inclusion a ∈ P
  surjective : ∀ T : H →L[ℂ] H, T ∈ P → ∃ a, inclusion a = T

theorem FiniteMatrixFactorModel.estimate {P : VonNeumannAlgebra H}
    (F : FiniteMatrixFactorModel P) : CommutatorEstimate P 2 := by
  have : NeZero F.size := ⟨F.size_ne_zero⟩
  exact finiteTypeI_commutator_estimate P F.inclusion F.mem F.surjective

/-- Increasing the numerical constant preserves the same estimate. -/
theorem CommutatorEstimate.mono {P : VonNeumannAlgebra H} {c C : ℝ}
    (h : CommutatorEstimate P c) (hc : c ≤ C) : CommutatorEstimate P C := by
  intro Y n X hX
  exact (h Y n X hX).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (scalarCommutatorNorm_nonneg P Y)) (norm_nonneg _))

/-- Precisely the factor alternatives needed downstream. The finite model
is supplied by Popa's increasing-matrix subfactor theorem and the listed
local inputs; the other two alternatives are projection/type classification. -/
def PublishedFactorCasesInput (P : VonNeumannAlgebra H) : Prop :=
  Nonempty (FiniteFactorModel P) ∨ HasInternalIsometryRows P ∨
    Nonempty (FiniteMatrixFactorModel P)

/-- All three structural alternatives yield the same fixed factor constant. -/
theorem factor_estimate_of_published_cases [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H)
    (cases : PublishedFactorCasesInput P)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H)) :
    CommutatorEstimate P factorConstant := by
  unfold PublishedFactorCasesInput at cases
  rcases cases with finite | infinite | matrix
  · obtain ⟨F⟩ := finite
    exact F.estimate.mono finiteFactorConstant_le
  · exact (properlyInfinite_commutatorEstimate P infinite dickson).mono infiniteFactorConstant_le
  · obtain ⟨F⟩ := matrix
    exact F.estimate.mono two_le_factorConstant

end KadisonSimilarity

end

end OAI
