import OAI.NumberTheory.Ostmann.InverseGoldbach
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothActualExplicitFormula
import OAI.NumberTheory.Ostmann.Preliminaries.MertensFromFirst
import OAI.NumberTheory.Ostmann.Characters.BonamiInput
import OAI.NumberTheory.Ostmann.ZeroDensity.MertensFromProgression
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothZeroCountFamily
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroCopies
import OAI.NumberTheory.Ostmann.Characters.CharacterFaithfulEnumeration
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualRealZeroExpansion
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualRealZeroRegion
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionConstantRestriction
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexRegionFromPage

namespace OAI

/-! # Analytic hypotheses for the inverse Goldbach theorem

Tensorization gives finite Bonami. The progression estimate gives the two
Mertens estimates and the principal smooth prime number theorem.
Multiplicity-labelled zero enumerations give the fixed-test explicit formula.
-/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_of_first_mertens
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM : ℝ) (hM : MertensEstimate CM)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    : TwoInfiniteSummandsImpossible := by
  exact twoInfiniteSummandsImpossible_of_published P0 ls hsize publishedBonamiBound Hreal hSiegel
    sieve CM _ hM hM.harmonic Z hD hR Pexplicit P0.smoothPrincipalPNT

theorem inverseGoldbach_of_first_mertens
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM : ℝ) (hM : MertensEstimate CM)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    : InverseGoldbach := by
  exact inverseGoldbach_of_published P0 ls hsize publishedBonamiBound Hreal hSiegel
    sieve CM _ hM hM.harmonic Z hD hR Pexplicit P0.smoothPrincipalPNT

/-- No independent Bonami, Mertens, or principal smooth PNT input remains. -/
theorem twoInfiniteSummandsImpossible_of_reduced_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_first_mertens P0 ls hsize Hreal hSiegel sieve
    P0.mertensConstant P0.mertens Z hD hR Pexplicit

/-- The exact inverse Goldbach conclusion with the same reduced input list. -/
theorem inverseGoldbach_of_reduced_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z) :
    InverseGoldbach :=
  inverseGoldbach_of_first_mertens P0 ls hsize Hreal hSiegel sieve
    P0.mertensConstant P0.mertens Z hD hR Pexplicit

/-- The analytic core implies the smoothness and absolute convergence needed
for the fixed-test explicit formula. -/
theorem twoInfiniteSummandsImpossible_of_analytic_core
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : SmoothExplicitFormulaCore Z) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_reduced_published P0 ls hsize Hreal hSiegel
    sieve Z hD hR Pexplicit.toPublished

/-- The exact main theorem after the same analytic input reduction. -/
theorem inverseGoldbach_of_analytic_core
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : SmoothExplicitFormulaCore Z) :
    InverseGoldbach :=
  inverseGoldbach_of_reduced_published P0 ls hsize Hreal hSiegel
    sieve Z hD hR Pexplicit.toPublished

/-- Multiplicity-labelled zero enumerations give the ordinary zero count. -/
theorem twoInfiniteSummandsImpossible_of_explicit_formula
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (hD : PublishedComplexZeroDensity (fun χ => characterZeroEnumeration χ (e χ)))
    (hR : PublishedComplexZeroRegion (fun χ => characterZeroEnumeration χ (e χ)))
    (E : ℝ) (hE : 0 < E)
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm (fun χ => characterZeroEnumeration χ (e χ)) χ X i) +
          smoothTrivialZeroTerm χ‖ ≤ E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_reduced_published P0 ls hsize Hreal hSiegel sieve
    (fun χ => characterZeroEnumeration χ (e χ)) hD hR
    (smoothExplicitFormula_of_multiplicity
      (fun χ => characterZeroEnumeration_respectsMultiplicity χ (e χ)) E hE hformula)

/-- The same explicit-formula-only reduction for manuscript Theorem 1.1. -/
theorem inverseGoldbach_of_explicit_formula
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (hD : PublishedComplexZeroDensity (fun χ => characterZeroEnumeration χ (e χ)))
    (hR : PublishedComplexZeroRegion (fun χ => characterZeroEnumeration χ (e χ)))
    (E : ℝ) (hE : 0 < E)
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm (fun χ => characterZeroEnumeration χ (e χ)) χ X i) +
          smoothTrivialZeroTerm χ‖ ≤ E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    InverseGoldbach :=
  inverseGoldbach_of_reduced_published P0 ls hsize Hreal hSiegel sieve
    (fun χ => characterZeroEnumeration χ (e χ)) hD hR
    (smoothExplicitFormula_of_multiplicity
      (fun χ => characterZeroEnumeration_respectsMultiplicity χ (e χ)) E hE hformula)

/-- A faithful numbering of the zeros gives the fixed-test explicit formula. -/
theorem twoInfiniteSummandsImpossible_of_numbered_zeros
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (hD : PublishedComplexZeroDensity (fun χ => characterZeroEnumeration χ (e χ)))
    (hR : PublishedComplexZeroRegion (fun χ => characterZeroEnumeration χ (e χ))) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_reduced_published P0 ls hsize Hreal hSiegel sieve
    (fun χ => characterZeroEnumeration χ (e χ)) hD hR (actualSmoothExplicitFormula e)

/-- The inverse Goldbach theorem using a faithful numbering of the zeros. -/
theorem inverseGoldbach_of_numbered_zeros
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (hD : PublishedComplexZeroDensity (fun χ => characterZeroEnumeration χ (e χ)))
    (hR : PublishedComplexZeroRegion (fun χ => characterZeroEnumeration χ (e χ))) :
    InverseGoldbach :=
  inverseGoldbach_of_reduced_published P0 ls hsize Hreal hSiegel sieve
    (fun χ => characterZeroEnumeration χ (e χ)) hD hR (actualSmoothExplicitFormula e)

/-- The zeros and smooth explicit formula come from the Dirichlet L-functions. -/
theorem twoInfiniteSummandsImpossible_of_remaining_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_numbered_zeros P0 ls hsize Hreal hSiegel sieve
    faithfulCharacterZeroEquiv hD hR

/-- The inverse Goldbach theorem using the Dirichlet L-function zeros. -/
theorem inverseGoldbach_of_remaining_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_numbered_zeros P0 ls hsize Hreal hSiegel sieve
    faithfulCharacterZeroEquiv hD hR

/-- The real Hadamard expansion gives the real-zero input from a low-height
zero-free region. -/
theorem twoInfiniteSummandsImpossible_of_actual_region
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (hregion : ActualRealLowHeightRegion P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_remaining_published P0 ls hsize
    (actualPublishedRealZeroInput P0 hregion) hSiegel sieve hD hR

/-- The inverse Goldbach theorem using the real low-height zero-free region. -/
theorem inverseGoldbach_of_actual_region
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (hregion : ActualRealLowHeightRegion P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_remaining_published P0 ls hsize
    (actualPublishedRealZeroInput P0 hregion) hSiegel sieve hD hR

/-- Restricting the progression constant to the absolute low-height constant
gives the real-character zero input. -/
theorem twoInfiniteSummandsImpossible_without_real_zero_input
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    TwoInfiniteSummandsImpossible := by
  obtain ⟨κ, hκ, hregion⟩ := exists_actual_real_low_height_region
  let P := P0.restrictKappa (min P0.kappa κ) (lt_min P0.kappa_pos hκ) (min_le_left _ _)
  exact twoInfiniteSummandsImpossible_of_actual_region P ls hsize
    (hregion P (min_le_right _ _)) hSiegel sieve hD hR

/-- The exact inverse Goldbach conclusion, with the real-character Hadamard
and low-height zero-free-region hypotheses both removed. -/
theorem inverseGoldbach_without_real_zero_input
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach := by
  obtain ⟨κ, hκ, hregion⟩ := exists_actual_real_low_height_region
  let P := P0.restrictKappa (min P0.kappa κ) (lt_min P0.kappa_pos hκ) (min_le_left _ _)
  exact inverseGoldbach_of_actual_region P ls hsize
    (hregion P (min_le_right _ _)) hSiegel sieve hD hR

/-- The progression estimate gives both zero regions using its real-zero
Page uniqueness clause. -/
theorem twoInfiniteSummandsImpossible_without_zero_region_inputs
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_real_zero_input P0 ls hsize hSiegel sieve hD
    P0.complexZeroRegion

/-- The exact inverse Goldbach conclusion with no independent zero-region,
Hadamard, explicit-formula or Mertens hypothesis. -/
theorem inverseGoldbach_without_zero_region_inputs
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_real_zero_input P0 ls hsize hSiegel sieve hD P0.complexZeroRegion

end Ostmann

end OAI
