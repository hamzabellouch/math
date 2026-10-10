import OAI.Analysis.KadisonSimilarity.Derivation.CyclicSpectralSum
import OAI.Analysis.KadisonSimilarity.Representation.RadonNikodymCoordinates
import OAI.Analysis.KadisonSimilarity.Representation.L2HilbertSum
import OAI.Analysis.KadisonSimilarity.Representation.HilbertSumIsometries
import OAI.Analysis.KadisonSimilarity.Representation.L2ScalarIntertwining

namespace OAI

/-! Embed the original separable Hilbert space into a single L² space by
placing its cyclic spectral coordinates over one finite dominating measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

local instance commonCyclicMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance commonCyclicBorel : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩
local instance commonCyclicCountable : Countable D.generators := D.generators_countable

def cyclicCommonBaseMeasure : Measure (WeakDual.characterSpace ℂ A) :=
  commonSpectralMeasure (fun i : D.generators => commutativeVectorMeasure π (i : H))

instance cyclicCommonBaseMeasure_finite : IsFiniteMeasure (cyclicCommonBaseMeasure π D) :=
  inferInstanceAs (IsFiniteMeasure (commonSpectralMeasure
    (fun i : D.generators => commutativeVectorMeasure π (i : H))))

instance cyclicCommonBaseMeasure_regular [TopologicalSpace.SeparableSpace A] :
    (cyclicCommonBaseMeasure π D).Regular := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) :=
    characterSpace_metrizable A
  infer_instance

abbrev CommonCyclicHilbert : Type _ :=
  Lp (ScalarHilbertCoordinates D.generators) 2 (cyclicCommonBaseMeasure π D)

def cyclicDensityIsometryData (i : D.generators) :
    {J : CyclicSpectralSpace π D i →ₗᵢ[ℂ] Lp ℂ 2 (cyclicCommonBaseMeasure π D) //
      ∀ (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i),
        J (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
          continuousL2Mul (cyclicCommonBaseMeasure π D) f (J ξ)} :=
  spectralDensityIntertwinerData (cyclicCommonBaseMeasure π D)
    (commutativeVectorMeasure π (i : H))
    (squareRootDensity (cyclicCommonBaseMeasure π D) (commutativeVectorMeasure π (i : H)))
    (squareRootDensity_measurable _ _)
    (squareRootDensity_memLp _ _ (component_absolutelyContinuous_common
      (fun j : D.generators => commutativeVectorMeasure π (j : H)) i))
    (squaredDensityMeasure_eq _ _ (component_absolutelyContinuous_common
      (fun j : D.generators => commutativeVectorMeasure π (j : H)) i))

def cyclicDensityIsometry (i : D.generators) : CyclicSpectralSpace π D i →ₗᵢ[ℂ]
    Lp ℂ 2 (cyclicCommonBaseMeasure π D) := (cyclicDensityIsometryData π D i).val

attribute [irreducible] cyclicDensityIsometryData cyclicDensityIsometry

def cyclicCommonFamilyData (i : D.generators) :
    {J : CyclicSpectralSpace π D i →ₗᵢ[ℂ] CommonCyclicHilbert π D //
      ∀ (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i),
        J (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
          VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f (J ξ)} := by
  classical
  exact coordinateIntertwinerData (cyclicCommonBaseMeasure π D)
    (commutativeVectorMeasure π (i : H)) (scalarCoordinateIsometry i)
    (cyclicDensityIsometryData π D i)

def cyclicCommonFamily (i : D.generators) : CyclicSpectralSpace π D i →ₗᵢ[ℂ]
    CommonCyclicHilbert π D := (cyclicCommonFamilyData π D i).val

theorem cyclicCommonFamily_orthogonal : OrthogonalFamily ℂ (CyclicSpectralSpace π D)
    (cyclicCommonFamily π D) := by
  classical
  change OrthogonalFamily ℂ _ (fun i =>
    (l2CoordinateIsometry (cyclicCommonBaseMeasure π D) i).comp
      (cyclicDensityIsometryData π D i).val)
  exact orthogonalFamily_comp_isometries _ (l2Coordinate_orthogonal _)
    (fun i => (cyclicDensityIsometryData π D i).val)

opaque cyclicCommonEmbeddingData :
    {J : H →ₗᵢ[ℂ] CommonCyclicHilbert π D //
      ∀ (i : D.generators) (ξ : CyclicSpectralSpace π D i),
        J ((cyclicSpectralSummands π D).inclusion i ξ) = cyclicCommonFamily π D i ξ} :=
  hilbertSumTransportWithComponents (cyclicSpectralSummands π D).inclusion
    (cyclicSpectral_isHilbertSum π D) (cyclicCommonFamily π D)
    (cyclicCommonFamily_orthogonal π D)

def cyclicCommonEmbedding : H →ₗᵢ[ℂ] CommonCyclicHilbert π D :=
  (cyclicCommonEmbeddingData π D).val

theorem cyclicCommonEmbedding_component (i : D.generators) (ξ : CyclicSpectralSpace π D i) :
    cyclicCommonEmbedding π D ((cyclicSpectralSummands π D).inclusion i ξ) =
      cyclicCommonFamily π D i ξ :=
  (cyclicCommonEmbeddingData π D).property i ξ

attribute [irreducible] cyclicCommonFamilyData cyclicCommonFamily
  cyclicCommonEmbedding

end KadisonSimilarity

end

end OAI
