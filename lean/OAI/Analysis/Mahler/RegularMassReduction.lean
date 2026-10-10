import OAI.Analysis.Mahler.EuclideanRegularLevels
import OAI.Analysis.Mahler.EuclideanMassDensity
import OAI.Analysis.Mahler.ComplexVolume
import OAI.Analysis.Mahler.ConvexMassReduction
import OAI.Analysis.Mahler.MassLimit

namespace OAI

namespace SymmetricMahler
open Set MeasureTheory

/-- The regular-level mass bound for the finite-strip map. -/
def SpecialRegularMassBound {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (m k : ℕ) : Prop :=
  ENNReal.ofReal ((stripRegularLevel k)^n * (Real.pi*(m : ℝ))^n) ≤
    Mahler.massBelow (euclideanStripDomain A) (euclideanSpecialMap A m) (stripRegularLevel k)

/-- The full body inequality follows from regular-level mass estimates for
the actual special maps alone. General Sard and a general mass theorem are
not needed by this reduction. -/
theorem symmetric_mahler_from_regular_special_mass {n : ℕ} (hn : 1 ≤ n)
    (hmass : ∀ N (A : Matrix (Fin N) (Fin n) ℝ), Function.Injective (measurement A) →
      ∀ m : ℕ, 2 ≤ m → ∀ k, SpecialRegularMassBound A m k)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4 : ℝ)^n/(Nat.factorial n : ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_of_special_gram_mass hn _ hK hconv hsym hint
  intro N A hA m hm
  have h := Mahler.massIntegral_lower_of_sublevels (euclideanStripDomain A)
    (euclideanSpecialMap A m) m tendsto_stripRegularLevel
    (fun k => (stripRegularLevel_mem k).2.le) (hmass N A hA m hm)
  rwa [euclideanSpecial_massIntegral (volume_preserving_complex_ofLp n) A m] at h

end SymmetricMahler

end OAI
