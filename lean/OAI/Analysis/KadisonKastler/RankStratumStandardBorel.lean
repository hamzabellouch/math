import OAI.Analysis.KadisonKastler.CommonRankCoordinates
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! # The common spectral rank strata are standard Borel spaces -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankStandardCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance rankStandardCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

theorem commonSpectralBase_standardBorel :
    StandardBorelSpace (WeakDual.characterSpace ℂ A) := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) := characterSpace_metrizable A
  let : MetricSpace (WeakDual.characterSpace ℂ A) := TopologicalSpace.metrizableSpaceMetric _
  let : SecondCountableTopology (WeakDual.characterSpace ℂ A) := characterSpace_secondCountable A
  infer_instance

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRankStratum_standardBorel (n : ℕ) :
    StandardBorelSpace (projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n) := by
  let : StandardBorelSpace (WeakDual.characterSpace ℂ A) := commonSpectralBase_standardBorel
  exact (measurableSet_projectionRankStratum (commonModelProjection M)
    (commonRankBasis π D) (commonModelProjection_measurable M) n).standardBorel

end

end KadisonKastler

end OAI
