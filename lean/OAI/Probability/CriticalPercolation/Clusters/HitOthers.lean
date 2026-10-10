import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open scoped Classical

variable {V : Type*} {n : ℕ}

noncomputable def hitOthers (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

lemma hitOthers_nonneg (x : Fin n → V) (k : Fin n) (U : Set V) :
    0 ≤ hitOthers x k U := by unfold hitOthers; positivity

lemma hitOthers_le_one (x : Fin n → V) (k : Fin n) (U : Set V) :
    hitOthers x k U ≤ 1 := by unfold hitOthers; split_ifs <;> norm_num

lemma hitOthers_monotone (x : Fin n → V) (k : Fin n) : Monotone (hitOthers x k) := by
  intro U W hUW
  unfold hitOthers
  split_ifs with hU hW hW
  · exact le_rfl
  · obtain ⟨j, hj, hjU⟩ := hU
    exact (hW ⟨j, hj, hUW hjU⟩).elim
  · norm_num
  · exact le_rfl

lemma hitOthers_singleton (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    hitOthers x k {x k} = 0 := by
  apply ite_eq_right
  rintro ⟨j, hj, hjk⟩
  exact hj (hx hjk)

end CriticalPercolation.ClusterColumns

end
end

end OAI
