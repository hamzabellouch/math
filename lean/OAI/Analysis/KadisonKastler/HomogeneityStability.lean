import OAI.Analysis.KadisonKastler.RepresentedProductBicentralizer
import OAI.Analysis.KadisonKastler.StateInputsStability

namespace OAI

/-! # Universal strong stability from faithful-state homogeneity alone

The concrete two-ratio product has a scalar bicentralizer and an expected
matrix subfactor in every required representation. Faithful-state
homogeneity supplies the state comparisons needed for the stability bound.
-/

namespace KadisonKastler
noncomputable section
universe u

/-- Modular core estimates independent of expected subfactors. -/
theorem constructedStabilityCoreInputs : ModularCorePublishedInputs.{u} := {
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
  correction := fun H _ _ _ M => publishedMultiplicationCorrection M }

/-- Connes--Størmer faithful-state homogeneity implies universal strong
stability, with one tolerance for all algebras and represented Hilbert spaces. -/
theorem universal_strong_stability_of_state_homogeneity
    (hhom : PublishedTypeIII1StateHomogeneity.{u}) : UniversalStrongStability.{u} := by
  let P : TwoRatioProductModel.{u} := concreteTwoRatioProductModel
  have hmodels : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
      (M : VonNeumannAlgebra H), ScalarCenter M →
      Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M P.stages.algebra)) := by
    intro H _ _ _ _ _ M hM
    have htype := P.tensor_typeIII1_general publishedModularSpectralResolution
      publishedKaplanskyDensity publishedRealSpectralCommutant publishedRealDiagonalDecomposition
      publishedFactorialModularCore H M hM
    exact P.coordinates.represented_expected_matrix_subfactor htype.toTypeIIIFactor
      (hhom _ _ htype)
  have hp := uniform_properlyInfinite_strong_stability_of_product_models
    constructedStabilityCoreInputs publishedModularSpectralResolution
    publishedFactorialModularCore publishedKaplanskyDensity P hmodels
  have hf := uniformFactorStability_of_properlyInfinite hp constructedStabilityCoreInputs.finite
    (fun H _ _ _ _ => publishedTypeIInjectivity) publishedInfiniteFactorProperlyInfinite
  exact universalStrongStability_of_factors hf publishedCentralPairDecomposition
    publishedKaplanskyDensity publishedUnitaryBorelSelection
    (fun H _ _ _ M => publishedDixmierAveraging M)
    (fun H _ _ _ M => publishedMultiplicationCorrection M)
    (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)

end
end KadisonKastler

end OAI
