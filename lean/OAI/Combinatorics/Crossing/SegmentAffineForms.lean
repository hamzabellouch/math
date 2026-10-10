import OAI.Combinatorics.Crossing.PlanarSegments

namespace OAI

namespace Zarankiewicz

theorem segmentPoint_start_form (a b : Plane) (t : ℝ) :
    segmentPoint a b t = a+t • (b-a) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

theorem segmentPoint_end_form (a b : Plane) (t : ℝ) :
    segmentPoint a b t = b-(1-t) • (b-a) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

end Zarankiewicz

end OAI
