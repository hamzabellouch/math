import OAI.Analysis.KadisonKastler.UniversalStability
import OAI.Analysis.KadisonKastler.TomiyamaField
import OAI.Analysis.KadisonKastler.FiniteType
import OAI.Analysis.KadisonKastler.RegularLocalizationReconstruction
import OAI.Analysis.KadisonKastler.SpectralCommutant
import OAI.Analysis.KadisonKastler.DiagonalDecomposition
import OAI.Analysis.KadisonKastler.ProperInfiniteProjectionCopies
import OAI.Analysis.KadisonKastler.VonNeumannSpectralCut
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.TwoRatioProductConstruction
import OAI.Analysis.KadisonKastler.PointedPowerProduct
import OAI.Analysis.KadisonKastler.KaplanskyDensity
import OAI.Analysis.KadisonKastler.TypeIInjectivity
import OAI.Analysis.KadisonKastler.InfiniteFactorProperInfiniteness
import OAI.Analysis.KadisonKastler.CentralAveragingLimit
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction
import OAI.Analysis.KadisonKastler.FactorialCoreSourceType
import OAI.Analysis.KadisonKastler.HardyEvaluationConstruction
import OAI.Analysis.KadisonKastler.CentralPairConstruction
import OAI.Analysis.KadisonKastler.SimpleDerivationConstruction
import OAI.Analysis.KadisonKastler.BoundaryConstruction
import OAI.Analysis.KadisonKastler.MultiplicationCorrectionConstruction

namespace OAI

/-! # Conditional strong stability from expected matrix subfactors

Existence of an expected matrix subfactor implies universal strong stability.
The other hypotheses of the general stability criterion follow from the
constructed operator-algebraic results.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Existence of expected matrix subfactors in the absorbed type III₁ setting. -/
structure RemainingStabilityPublishedInputs : Prop where
  expected : PublishedExpectedMatrixSubfactor.{u}

/-- Expected matrix subfactors supply the hypotheses of the general stability criterion. -/
theorem RemainingStabilityPublishedInputs.toPublished
    (h : RemainingStabilityPublishedInputs.{u}) : UniversalStabilityPublishedInputs.{u} where
  finite := {
    boundary := publishedBoundary
    tomiyama := by
      intro H _ _ _ _ G D _ _ _ _ μ _
      exact publishedFieldTomiyama
    finiteType := fun H _ _ _ _ => publishedFiniteType }
  coreCommutant := publishedRegularCommutant
  realSpectral := publishedRealSpectralCommutant
  diagonal := publishedRealDiagonalDecomposition
  copies := publishedProperInfiniteProjectionCopies
  spectral := publishedVonNeumannSpectralCut
  comparison := publishedTypeIIIProjectionComparison
  sakai := publishedSimpleDerivationInner
  hardy := publishedHardyMultiplierEvaluation
  correction := fun H _ _ _ M => publishedMultiplicationCorrection M
  product := publishedTwoRatioProduct
  pointed := publishedPointedMatrixOperations
  modular := publishedModularSpectralResolution
  coreClassification := publishedFactorialModularCore
  kaplansky := publishedKaplanskyDensity
  expected := h.expected
  typeI := fun H _ _ _ _ => publishedTypeIInjectivity
  infiniteType := publishedInfiniteFactorProperlyInfinite
  central := publishedCentralPairDecomposition
  dixmier := fun H _ _ _ M => publishedDixmierAveraging M

/-- Expected matrix subfactors imply the universal stability statement.
Its tolerance precedes every representation. -/
theorem universal_strong_stability_of_remaining
    (h : RemainingStabilityPublishedInputs.{u}) : UniversalStrongStability.{u} :=
  universal_strong_stability_of_published h.toPublished

end

end KadisonKastler

end OAI
