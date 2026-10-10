import OAI.Analysis.BoundedHochschild.ProperlyInfinitePrimitives
import OAI.Analysis.BoundedHochschild.AveragedBarFaces
import OAI.Analysis.BoundedHochschild.NormalBarOperators
import OAI.Analysis.BoundedHochschild.MatrixBarLimits
import OAI.Analysis.BoundedHochschild.BarInsertionFormula
import OAI.Analysis.BoundedHochschild.CountableMatrixProjection
import OAI.Analysis.BoundedHochschild.AlgebraicMatrixPrimitives
import OAI.Analysis.BoundedHochschild.MultimodularInsertion
import OAI.Analysis.BoundedHochschild.MatrixAverageLimits
import OAI.Analysis.BoundedHochschild.NormalCochainTransport
import OAI.Analysis.BoundedHochschild.FiniteGroupModuleAverages
import OAI.Analysis.BoundedHochschild.CountableMatrixGroups
import OAI.Analysis.BoundedHochschild.MultimodularGenerators
import OAI.Analysis.BoundedHochschild.NormalMultimodularClosure
import OAI.Analysis.BoundedHochschild.CountableMatrixPrimitives
import OAI.Analysis.BoundedHochschild.MultimodularMatrixBound
import OAI.Analysis.BoundedHochschild.CompletelyBoundedPrimitives
import OAI.Analysis.BoundedHochschild.RightModuleProjection
import OAI.Analysis.BoundedHochschild.Conditional
import OAI.Analysis.BoundedHochschild.CentralVanishing
import OAI.Analysis.BoundedHochschild.TracialDecomposition
import OAI.Analysis.BoundedHochschild.AbelianPrimitives
import OAI.Analysis.BoundedHochschild.OperatorTypeI
import OAI.Analysis.BoundedHochschild.AbelianTypeI
import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition
import OAI.Analysis.BoundedHochschild.TypeICentralDecomposition
import OAI.Analysis.BoundedHochschild.CenterAveragingReduction
import OAI.Analysis.BoundedHochschild.NormalStatePartitions
import OAI.Analysis.BoundedHochschild.TraceFreeComparison
import OAI.Analysis.BoundedHochschild.TypeIICharacterization
import OAI.Analysis.BoundedHochschild.FiniteIncreasingComparison
import OAI.Analysis.BoundedHochschild.NormalOrbitHull
import OAI.Analysis.BoundedHochschild.NormalOrderIntervals
import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums
import OAI.Analysis.BoundedHochschild.PositiveCompleteAdditivity
import OAI.Analysis.BoundedHochschild.WeakPredual
import OAI.Analysis.BoundedHochschild.MinimalIsometricOrbit
import OAI.Analysis.BoundedHochschild.FiniteTracialDecomposition
import OAI.Analysis.BoundedHochschild.HomogeneousTypeIPrimitives
import OAI.Analysis.BoundedHochschild.FiniteTypeIVanishing
import OAI.Analysis.BoundedHochschild.ClassicalVanishingReduction
import OAI.Analysis.BoundedHochschild.InfiniteMatrixColumns
import OAI.Analysis.BoundedHochschild.ProperlyInfiniteMatrixSystems
import OAI.Analysis.BoundedHochschild.MatrixAmplification
import OAI.Analysis.BoundedHochschild.CompletelyBoundedRows
import OAI.Analysis.BoundedHochschild.MinimalRightAverages
import OAI.Analysis.BoundedHochschild.RightModuleFixedPoints
import OAI.Analysis.BoundedHochschild.WeakCompletelyBoundedClosure
import OAI.Analysis.BoundedHochschild.NormalGNSWeakTopology
import OAI.Analysis.BoundedHochschild.NormalGNSMatrices
import OAI.Analysis.BoundedHochschild.StinespringEmbedding
import OAI.Analysis.BoundedHochschild.UnitalPositiveExtension
import OAI.Analysis.BoundedHochschild.PositiveUnitBlocks
import OAI.Analysis.BoundedHochschild.CompletelyBoundedFactorization
import OAI.Analysis.BoundedHochschild.NormalFactorCandidates
import OAI.Analysis.BoundedHochschild.RepresentedAveragingConvexity
import OAI.Analysis.BoundedHochschild.AveragingOrbitFactorization
import OAI.Analysis.BoundedHochschild.InfiniteAveragingLimits
import OAI.Analysis.BoundedHochschild.InfiniteInvariantFamilies
import OAI.Analysis.BoundedHochschild.InfiniteRepresentedFamilies
import OAI.Analysis.BoundedHochschild.CentralSupportNormalizedRows
import OAI.Analysis.BoundedHochschild.PositiveProjectionGap
import OAI.Analysis.BoundedHochschild.RightModuleAveragingExistence
import OAI.Analysis.BoundedHochschild.SimultaneousModuleAverages

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open scoped ComplexOrder

universe u

/-- Every bounded higher cocycle on a von Neumann algebra has a bounded
primitive. No complete-boundedness or normality assumption is required. -/
theorem bounded_primitive
    {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ} (f : Cochain M (n + 2))
    (hf : differential f = 0) :
    ∃ g : Cochain M (n + 1), differential g = f := by
  obtain ⟨g, hg⟩ := primitive_of_properlyInfinite_input e properlyInfiniteVanishingInput f
    ((differential_eq_zero_iff f).mp hf)
  refine ⟨g, ?_⟩
  ext x
  simpa only [differential_apply] using hg x

/-- Theorem 1.1: ordinary bounded Hochschild cohomology vanishes in every
degree at least two, with the actual image of the differential. -/
theorem vanishing
    {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (k : ℕ) (hk : 2 ≤ k) :
    (∀ f : Cochain M k, differential f = 0 →
      ∃ g : Cochain M (k - 1), incomingDifferential M k g = f) ∧
    Subsingleton (Cohomology M k) := by
  obtain ⟨X, hX, hXS, hXC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
  let := hX
  let := hXS
  let := hXC
  exact vanishing_of_published_inputs (centralDecompositionInput e) classicalVanishingInput k hk

/-- A separately normal higher cocycle on a tracial type II₁ algebra has an
actual bounded primitive with norm at most its own norm. -/
theorem normal_tracial_primitive
    {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0) (h1 : τ 1 = 1)
    (hII : PopaTypeII.NoTypeICentralPart M) {n : ℕ}
    (f : Cochain M (n + 2)) (hf : differential f = 0)
    (hn : SeparatelyNormal e f) :
    ∃ g : Cochain M (n + 1), ‖g‖ ≤ ‖f‖ ∧ differential g = f := by
  obtain ⟨g, hgn, hg⟩ := source_tracial_primitive e τ hτ htr hfaith h1 hII f
    ((differential_eq_zero_iff f).mp hf)
    ((separatelyNormal_iff_tracialSeparatelyNormal e f).mp hn)
  refine ⟨g, hgn, ?_⟩
  ext x
  simpa only [differential_apply] using hg x

end KadisonRingrose
end BoundedHochschild

end

end OAI
