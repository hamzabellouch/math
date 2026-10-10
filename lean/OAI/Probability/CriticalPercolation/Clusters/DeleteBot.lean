import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}
@[simp] lemma delete_bot (U : Set V) : delete (⊥ : SimpleGraph V) U = ⊥ := by
  ext v w
  simp [delete]
@[simp] lemma component_bot (s : V) : component (⊥ : SimpleGraph V) s = {s} := by
  ext v
  simp [component, SimpleGraph.reachable_bot, eq_comm]
@[simp] lemma roots_bot (S : Set V) : roots (⊥ : SimpleGraph V) S = S := by
  ext v
  simp [roots, SimpleGraph.reachable_bot]
end CriticalPercolation.ClusterDeletion

end
end

end OAI
