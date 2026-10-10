import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestMap

namespace OAI

namespace MetricKMedianRecovery.HistoryIsometry
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [DecidableEq X] [DecidableEq Y]

omit [Fintype D] [DecidableEq X] in
lemma clipped_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) :
    clippedAt (fun a => r (loc a)) t z (Q.image r) j = clippedAt loc t z Q j := by
  unfold clippedAt
  simp only [Finset.image_nonempty,nearest_map r hr]

omit [DecidableEq X] in
lemma row_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) :
    bidRow (fun a => r (loc a)) t z (Q.image r) (r i) = bidRow loc t z Q i := by
  simp only [bidRow,clipped_map r hr,hr]

end MetricKMedianRecovery.HistoryIsometry

end OAI
