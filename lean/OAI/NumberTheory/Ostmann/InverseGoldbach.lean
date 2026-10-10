import OAI.NumberTheory.Ostmann.Construction.ConditionalMain
import OAI.NumberTheory.Ostmann.FiniteSummands

namespace OAI

/-! # Ostmann's inverse Goldbach theorem, conditional on the published inputs -/
namespace Ostmann

/-- Theorem 1.1: every sum of two nontrivial sets has infinite symmetric
difference with the primes. The finite-summand reduction uses Mathlib's
Dirichlet theorem; the infinite-summand theorem carries the listed published
analytic inputs explicitly. -/
theorem inverseGoldbach_of_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) : InverseGoldbach := by
  intro A B hA hB hfinite
  have hsum := (finite_symmDiff_iff A B).mp hfinite
  obtain ⟨hAinf, hBinf⟩ := infinite_summands hA hB hsum
  exact twoInfiniteSummandsImpossible_of_published P0 ls hsize hBonami Hreal hSiegel sieve
    CM CH hM hMH Z hD hR Pexplicit hPNT A B hAinf hBinf hsum

end Ostmann

end OAI
