import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*}

noncomputable def hitValue (A U : Set V) : ℝ := if (U ∩ A).Nonempty then 1 else 0
noncomputable def jointHitValue (A T U : Set V) : ℝ :=
  if (U ∩ A).Nonempty ∧ (U ∩ T).Nonempty then 1 else 0

lemma hitValue_nonneg (A U : Set V) : 0 ≤ hitValue A U := by unfold hitValue; positivity
lemma hitValue_le_one (A U : Set V) : hitValue A U ≤ 1 := by unfold hitValue; split_ifs <;> norm_num
lemma hitValue_monotone (A : Set V) : Monotone (hitValue A) := by
  intro U W hUW
  unfold hitValue
  split_ifs with hU hW hW
  · exact le_rfl
  · exact (hW (hU.mono (Set.inter_subset_inter_left A hUW))).elim
  · norm_num
  · exact le_rfl

lemma jointHitValue_nonneg (A T U : Set V) : 0 ≤ jointHitValue A T U := by
  unfold jointHitValue; positivity
lemma jointHitValue_monotone (A T : Set V) : Monotone (jointHitValue A T) := by
  intro U W hUW
  unfold jointHitValue
  split_ifs with hU hW hW
  · exact le_rfl
  · exact (hW ⟨hU.1.mono (Set.inter_subset_inter_left A hUW),
      hU.2.mono (Set.inter_subset_inter_left T hUW)⟩).elim
  · norm_num
  · exact le_rfl

lemma jointHitValue_eq_hitValue {A T U : Set V} (hA : (U ∩ A).Nonempty) :
    jointHitValue A T U = hitValue T U := by simp [jointHitValue, hitValue, hA]

lemma component_inter_nonempty_iff (H : SimpleGraph V) (s : V) (A : Set V) :
    (component H s ∩ A).Nonempty ↔ s ∈ roots H A := by
  constructor
  · rintro ⟨t, ht, hA⟩
    exact ⟨t, hA, ht.symm⟩
  · rintro ⟨t, hA, ht⟩
    exact ⟨t, ht.symm, hA⟩

end CriticalPercolation.ClusterColumns

end
end

end OAI
