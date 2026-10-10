import Mathlib
import OAI.Geometry.SmoothYau.Estimates.SphericalWitnessesUnbounded
import OAI.Geometry.SmoothYau.Limits.SphericalFixedFormNorm

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem sphere_three (gRound : SmoothMetric (Euclidean 3) (Sphere 3))
    (hRound : IsRound gRound) :
    ∀ N : Set (SmoothMetric (Euclidean 3) (Sphere 3)),
      IsSmoothNeighborhood gRound N →
      ∃ g ∈ N, HasUnboundedNodalRatio g 3 := by
  intro N hN
  obtain ⟨g,hgN,hg⟩ := exists_spherical_fixed_witnesses gRound hRound N hN
  exact ⟨g,hgN,spherical_witnesses_unbounded g hg⟩
end YauCounterexamples
end

end OAI
