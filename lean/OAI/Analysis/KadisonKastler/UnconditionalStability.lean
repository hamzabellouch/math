import OAI.Analysis.KadisonKastler.HomogeneityStability
import OAI.Analysis.KadisonKastler.RepresentedProductHomogeneity

namespace OAI

/-! # Universal strong Kadison--Kastler stability

The two-ratio product's faithful-state homogeneity follows from its modular
coisometries. Its expected matrix subfactor is constructed in the original
representation. These constructions give a tolerance uniform over all
Hilbert spaces and represented von Neumann algebras.
-/

namespace KadisonKastler
noncomputable section
universe u

theorem unconditional_properlyInfinite_strong_stability :
    UniformProperInfiniteFactorStability.{u} := by
  let P : TwoRatioProductModel.{u} := concreteTwoRatioProductModel
  have hmodels : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
      (M : VonNeumannAlgebra H), ScalarCenter M →
      Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M P.stages.algebra)) := by
    intro H _ _ _ _ _ M hM
    have htype := P.tensor_typeIII1_general publishedModularSpectralResolution
      publishedKaplanskyDensity publishedRealSpectralCommutant publishedRealDiagonalDecomposition
      publishedFactorialModularCore H M hM
    exact P.coordinates.constructed_represented_expected_matrix_subfactor htype.toTypeIIIFactor
  exact uniform_properlyInfinite_strong_stability_of_product_models
    constructedStabilityCoreInputs publishedModularSpectralResolution
    publishedFactorialModularCore publishedKaplanskyDensity P hmodels

theorem uniform_factor_strong_stability : UniformFactorStability.{u} :=
  uniformFactorStability_of_properlyInfinite unconditional_properlyInfinite_strong_stability
    constructedStabilityCoreInputs.finite (fun _H _ _ _ _ => publishedTypeIInjectivity)
    publishedInfiniteFactorProperlyInfinite

/-- Theorem 1.1 of *Universal strong Kadison–Kastler stability*, at every universe level. The
tolerance is chosen before the Hilbert space and both represented algebras. -/
theorem universal_strong_stability : UniversalStrongStability.{u} :=
  universalStrongStability_of_factors uniform_factor_strong_stability
    publishedCentralPairDecomposition publishedKaplanskyDensity publishedUnitaryBorelSelection
    (fun _H _ _ _ M => publishedDixmierAveraging M)
    (fun _H _ _ _ M => publishedMultiplicationCorrection M)
    (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)

end
end KadisonKastler

end OAI
