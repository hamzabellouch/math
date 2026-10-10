import OAI.NumberTheory.DirichletL.Reflection.MarkedActiveSets

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

lemma markedActiveEquiv_frozen (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (b : B) :
    (markedActiveEquiv e B T (Sum.inl b)).val=Sum.inl (e (Sum.inr b.val)) := rfl
lemma markedActiveEquiv_residual (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (a : α) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inl a))).val=Sum.inl (e (Sum.inl a)) := rfl
lemma markedActiveEquiv_slot (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (t : T) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inr t))).val=Sum.inr t.val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
