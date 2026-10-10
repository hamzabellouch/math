import OAI.Analysis.Mahler.ConvexENNRealTransfer
import OAI.Analysis.Mahler.ConvexPolarBody
import OAI.Analysis.Mahler.SpecialMassBridge

namespace OAI

namespace SymmetricMahler
open Set MeasureTheory
open scoped ENNReal

/-- Reduction of the full symmetric convex-body theorem to the exact complex
mass inequality. The remaining analytic premise is displayed explicitly. -/
theorem symmetric_mahler_of_special_gram_mass {n : ℕ} (hn : 1 ≤ n)
    (hmass : ∀ N (A : Matrix (Fin N) (Fin n) ℝ), Function.Injective (measurement A) →
      ∀ m : ℕ, 2 ≤ m →
        ENNReal.ofReal ((Real.pi * (m : ℝ)) ^ n) ≤
          ∫⁻ z in specialSublevel A m,
            ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m z))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4 : ℝ) ^ n / (Nat.factorial n : ℝ) ≤
      (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_of_finite_strips_ennreal hn _ hK hconv hsym hint
  intro N A hA
  apply finite_strip_mahler_of_mass A hA
  intro m hm
  exact stripMassBound_of_special_gram_mass A hm (hmass N A hA m hm)

end SymmetricMahler

end OAI
