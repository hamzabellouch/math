import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Scalar.ScalarPrefixCoefficient

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedList_field_bound (w : List (ℝ × (ℝ × ℝ))) (j : Fin (w.length+1)) :
    |scalarLevelField w.length (fun i => (w.get i).2.1) j
      (coordinateVector w.length (fun i => (w.get i).2.2))| ≤ weightedAbsCross w := by
  rw [scalarLevelField_vector]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold weightedAbsCross
  rw [← sum_get_map w (fun p => |p.2.2| * |p.2.1|)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp only [abs_mul,abs_zero,le_refl]
  positivity

end SK.Analytic

end
end

end OAI
