import OAI.Analysis.Mahler.SourceRadiusFlux
import OAI.Analysis.Mahler.SpecialSourceMass

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Mahler

/-- Stokes and the sphere limit reduce the mass inequality
to the numerical homogeneous sphere flux. -/
theorem MassHypotheses.regular_massBelow_of_homogeneous_value {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hvalue : homogeneousSphereFlux k N G = (Real.pi*(m:ℝ))^(k+1)) :
    ENNReal.ofReal (R^(k+1)*(Real.pi*(m:ℝ))^(k+1)) ≤ massBelow U f R := by
  apply source_regular_massBelow_of_flux_limit h hR hR1 hreg
  simpa only [hvalue] using h.sourceCoordinateFlux_limit

end Mahler
namespace SymmetricMahler

/-- The final body theorem needs the homogeneous value only for the actual
finite-strip polynomial family. A general isolated-zero mass theorem or
Sard theorem is not an additional premise. -/
theorem symmetric_mahler_from_special_homogeneous_values (n : ℕ)
    (hvalue : ∀ N (A : Matrix (Fin N) (Fin (n+1)) ℝ),
      Function.Injective (measurement A) → ∀ m : ℕ, 2 ≤ m →
      Mahler.homogeneousSphereFlux n N (specialLeadingPolynomial A m) =
        (Real.pi*(m:ℝ))^(n+1))
    {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_from_special_source_flux_limits n _ hK hconv hsym hint
  intro N A hA m hm
  have h := euclideanSpecial_massHypotheses A (by omega) hA hm
  simpa only [hvalue N A hA m hm] using h.sourceCoordinateFlux_limit

end SymmetricMahler

end

end OAI
