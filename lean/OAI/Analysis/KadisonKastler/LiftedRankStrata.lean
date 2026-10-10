import OAI.Analysis.KadisonKastler.RankStratumStandardBorel
import OAI.Analysis.KadisonKastler.L2CoordinateEquiv
import OAI.Analysis.KadisonKastler.BlockCoordinateTransport
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition
import OAI.Analysis.KadisonKastler.HilbertSpaceLift

namespace OAI

/-! # Rank strata in the universe of the original Hilbert space -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {A B H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def rankFiberLift (n : ℕ) :
    ℓ²(projectionDimensionIndex n, ℂ) ≃ₗᵢ[ℂ] ULift.{u} ℓ²(projectionDimensionIndex n, ℂ) :=
  (LinearIsometryEquiv.ulift ℂ ℓ²(projectionDimensionIndex n, ℂ)).symm

def commonRankStratum (n : ℕ) : MeasuredHilbertStratum.{u} := by
  let : TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
    separable_scalarHilbertCoordinates
  let : TopologicalSpace.SeparableSpace (ULift.{u} ℓ²(projectionDimensionIndex n, ℂ)) :=
    hilbertULift_separable
  let : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) := borel _
  let : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
  exact {
    X := projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n
    measurableX := inferInstance
    standardX := commonRankStratum_standardBorel M n
    K := ULift.{u} ℓ²(projectionDimensionIndex n, ℂ)
    normedK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    separableK := inferInstance
    measurableK := inferInstance
    borelK := inferInstance
    μ := projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) n
    finiteμ := inferInstance }

def commonRankStratumEquiv (n : ℕ) :
    Lp ℓ²(projectionDimensionIndex n, ℂ) 2
      (projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
        (commonRankBasis π D) n) ≃ₗᵢ[ℂ] (commonRankStratum M n).space :=
  l2CoordinateEquiv _ (rankFiberLift n)

def liftedRankCoordinates : H ≃ₗᵢ[ℂ] lp (fun n => (commonRankStratum M n).space) 2 :=
  (commonRankCoordinates M).trans (hilbertSumCoordinateEquiv (commonRankStratumEquiv M))

def liftedRankRepresentation (n : ℕ) (x : (commonRankStratum M n).X) :
    B →⋆ₐ[ℂ] ((commonRankStratum M n).K →L[ℂ] (commonRankStratum M n).K) :=
  (rankFiberLift n).conjStarAlgEquiv.toStarAlgHom.comp
    (fixedFiberRepresentation M.field (commonRankBasis π D) (commonRankBasis_total π D) n x)

omit [TopologicalSpace.SeparableSpace B] in
theorem liftedRankRepresentation_measurable (n : ℕ) (a : B) (v : (commonRankStratum M n).K) :
    Measurable fun x => liftedRankRepresentation M n x a v := by
  let : MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
  let : BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩
  let : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) := borel _
  let : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
  change Measurable fun x => rankFiberLift n
    (fixedFiberRepresentation M.field (commonRankBasis π D) (commonRankBasis_total π D)
      n x a ((rankFiberLift n).symm v))
  exact (rankFiberLift n).continuous.measurable.comp
    (fixedFiberRepresentation_measurable M.field (commonRankBasis π D) (commonRankBasis_total π D)
      M.measurable n a ((rankFiberLift n).symm v))

end

end KadisonKastler

end OAI
