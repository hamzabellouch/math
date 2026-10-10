import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeodesicWords

namespace OAI

/-! # Bounded words from the published large-scale chain metric -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

/-- Consecutive group differences telescope to the original element. The
published chain metric suffices; minimizing paths are unnecessary. -/
theorem LinearMetricChains.wordFactorization
    {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (C : LinearMetricChains G) (g : G) :
    ∃ w : List G, (∀ q ∈ w, q ∈ closedBall 1 C.step) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ C.slope * dist 1 g + C.error := by
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := C.chain 1 g
  let w := (List.range n).map (fun k => (p k)⁻¹ * p (k + 1))
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    rw [mem_closedBall, dist_comm, dist_one_groupDifference]
    exact hp k (List.mem_range.mp hk)
  · have he := List.prod_range_div' n (fun k => (p k)⁻¹)
    simpa only [w, div_eq_mul_inv, inv_inv, hp0, hpn, inv_one, one_mul] using he
  · simpa only [w, List.length_map, List.length_range] using hn

end PolycyclicRecognition

end

end OAI
