import OAI.Analysis.Mahler.SourceRadiusFlux
import OAI.Analysis.Mahler.SpecialSourceMass
import OAI.Analysis.Mahler.HomogeneousTwoFlux
import OAI.Analysis.Mahler.HomogeneousCircleIntegral

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

/-- The symmetric Mahler body inequality in dimension one. -/
theorem symmetric_mahler_dimension_one
    {K : Set (Fin 1 → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    4 ≤ (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  have hb := symmetric_mahler_from_special_source_flux_limits 0 (fun N A hA m hm => by
    have h := euclideanSpecial_massHypotheses A (by omega) hA hm
    have ht := h.sourceCoordinateFlux_limit
    simpa only [h.homogeneousCircle_flux, Nat.zero_add, pow_one] using ht) hK hconv hsym hint
  norm_num at hb
  exact hb

/-- The symmetric Mahler body inequality in dimension two, using the
coordinate/radius identity and the dimension-two homogeneous flux value;
no flux, mass, regularity or approximation conclusion is an extra premise. -/
theorem symmetric_mahler_dimension_two
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    8 ≤ (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  have hb := symmetric_mahler_from_special_source_flux_limits 1 (fun N A hA m hm => by
    have h := euclideanSpecial_massHypotheses A (by omega) hA hm
    have ht := h.sourceCoordinateFlux_limit
    simpa only [h.homogeneousSphereFlux_two_value] using ht) hK hconv hsym hint
  norm_num at hb
  exact hb

end SymmetricMahler

end

end OAI
