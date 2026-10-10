import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionCount

namespace OAI

/-! # A completion-coordinate change in the finite transition count -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma booleanFinish_equiv_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] {s f Q : ℕ} (p : IntegerLaw A (2^f)) (q : IntegerLaw B Q)
    (e : A ≃ B) (M : ℕ) (finish : (Fin s → Bool) → B → C)
    (h : ∀ a,p.count a=q.count (e a)*M) (c : C) :
    (booleanFinish p (fun bits a => finish bits (e a))).count c=
      ∑ bits : Fin s → Bool,∑ b,if finish bits b=c then q.count b*M else 0 := by
  rw [booleanFinish_count]
  simp_rw [h]
  apply Finset.sum_congr rfl
  intro bits _
  exact e.sum_comp (fun b : B => if finish bits b=c then q.count b*M else 0)

end
end ContingencyTables.IntegerLaw

end OAI
