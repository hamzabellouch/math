import OAI.Combinatorics.ContingencyTables.Transport.IntegerEquivLaw

namespace OAI

/-! # Count transport through a completion-coordinate bijection -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma push_equiv_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] {P Q : ℕ} (p : IntegerLaw A P) (q : IntegerLaw B Q)
    (e : A ≃ B) (M : ℕ) (finish : B → C)
    (h : ∀ a,p.count a=q.count (e a)*M) (c : C) :
    (p.push (fun a => finish (e a))).count c=
      ∑ b,if finish b=c then q.count b*M else 0 := by
  change (∑ a,if finish (e a)=c then p.count a else 0)=_
  simp_rw [h]
  exact e.sum_comp (fun b : B => if finish b=c then q.count b*M else 0)

end
end ContingencyTables.IntegerLaw

end OAI
