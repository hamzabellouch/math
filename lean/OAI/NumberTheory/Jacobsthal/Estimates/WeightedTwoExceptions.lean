import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEligible
attribute [local instance] Classical.propDecidable

theorem weighted_two_exceptions {α : Type*} (S : Finset α) (weight : α → ℝ)
    (E A B : α → Prop) (hw : ∀ x ∈ S,0 ≤ weight x)
    (hsub : ∀ x ∈ S,E x → A x ∨ B x) :
    (∑ x ∈ S.filter E,weight x) ≤ (∑ x ∈ S.filter A,weight x)+(∑ x ∈ S.filter B,weight x) := by
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : E x
  · rcases hsub x hx he with ha|hb
    · simp only [ite_eq_left he,ite_eq_left ha]
      split_ifs <;> linarith [hw x hx]
    · simp only [ite_eq_left he,ite_eq_left hb]
      split_ifs <;> linarith [hw x hx]
  · simp only [ite_eq_right he]
    split_ifs <;> linarith [hw x hx]

end ErdosVarianceEligible

end

end Erdos970

end OAI
