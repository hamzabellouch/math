import OAI.Analysis.Mahler.HomogeneousEndpoint
import OAI.Analysis.Mahler.HomogeneousMassAssembly

namespace OAI

noncomputable section
open Set MeasureTheory
namespace SymmetricMahler

/-- The symmetric Mahler inequality in every positive
dimension, for ordinary Lebesgue volume and the coordinate polar. -/
theorem symmetric_mahler {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^n/(Nat.factorial n:ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  cases n with
  | zero => omega
  | succ k =>
    apply symmetric_mahler_from_special_homogeneous_values k _ hK hconv hsym hint
    intro N A hA m hm
    exact (euclideanSpecial_massHypotheses A (by omega) hA hm).homogeneousSphereFlux_value

end SymmetricMahler

end

end OAI
