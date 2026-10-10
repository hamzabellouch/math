import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Rat.Encodable

namespace OAI

/-! # A countable compact exhaustion of each open metric ball -/

open Set Metric

namespace RegularPointCoordinates

variable {X : Type*} [PseudoMetricSpace X]

theorem ball_eq_iUnion_rational_closedBall (p : X) (R : ℝ) :
    ball p R=⋃ q : {q : ℚ // (q:ℝ)<R}, closedBall p (q.val:ℝ) := by
  ext x
  constructor
  · intro hx
    change dist x p<R at hx
    obtain ⟨q,hxq,hqR⟩ := exists_rat_btwn hx
    exact mem_iUnion.mpr ⟨⟨q,hqR⟩,hxq.le⟩
  · intro hx
    obtain ⟨q,hxq⟩ := mem_iUnion.mp hx
    change dist x p≤(q.val:ℝ) at hxq
    exact lt_of_le_of_lt hxq q.property

end RegularPointCoordinates

end OAI
