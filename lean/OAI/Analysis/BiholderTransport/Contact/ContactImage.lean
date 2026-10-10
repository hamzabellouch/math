import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section ContactImage
variable {M : Type*} [MetricSpace M]

lemma contactGap_swap (u v : M → ℝ) (x y : M) :
    contactGap u v x y=contactGap v u y x := by
  simp only [contactGap,cost,dist_comm y x]
  ring

variable [MeasurableSpace M]
end ContactImage

end WeakMTWTransport
end
end
end

end OAI
