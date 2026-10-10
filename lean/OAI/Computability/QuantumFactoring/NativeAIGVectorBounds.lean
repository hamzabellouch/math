import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGShift
import OAI.Computability.QuantumFactoring.NativeAIGIfProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
lemma shift_length (xs : List Ref) (d : ℕ) : (shift xs d).length=xs.length := by
  simp [shift]
lemma shift_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) (d : ℕ) :
    RefsBound B (shift xs d) := by
  refine ⟨by simpa only [shift_length] using h.1,?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  unfold shiftBit
  split
  · exact Nat.zero_le _
  · exact h.get _
lemma addStep_length (s : AddState) : (addStep s).val.output.length=s.val.output.length+1 := by
  simp only [addStep,addStepData,List.length_append,List.length_singleton]
lemma addStep_iterate_length (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_length];omega
lemma addBlastState_length (s : AddState) : (addBlastState s).val.output.length=s.val.lhs.length := by
  rw [addBlastState,addStep_iterate_length]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]
lemma addState_length (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.output.length=s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_length s
  · rw [addBlastState_length];exact h.symm
lemma addState_budget_eq (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.budget=s.val.budget+13*s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_budget s
  · rw [addBlastState_budget];change s.val.budget+13*s.val.rhs.length=_;rw [h]
lemma ifStep_length (s : AddState) : (ifStep s).val.output.length=s.val.output.length+1 := by
  simp only [ifStep,ifStepData,List.length_append,List.length_singleton]
lemma ifStep_iterate_length (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_length];omega
lemma ifVecState_length (s : AddState) : (ifVecState s).val.output.length=s.val.lhs.length := by
  rw [ifVecState,ifStep_iterate_length]
  simp only [initializeIf,initializeIfData,List.length_nil,Nat.zero_add]
lemma add_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (he : lhs.length=rhs.length) :
    Bounded (B+13*lhs.length) (add g lhs rhs).1 ∧
    RefsBound (B+13*lhs.length) (add g lhs rhs).2 ∧ (add g lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hs : s.val.lhs.length=s.val.rhs.length:=he
  have hb:=addState_budget_eq s hs
  have ho:=(addState s).property
  have hv:=addState_value s
  have hn:=addState_length s hs
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
lemma ifVec_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref} {c : Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (hc : c.1 ≤ B) :
    Bounded (B+3*lhs.length) (ifVec g c lhs rhs).1 ∧
    RefsBound (B+3*lhs.length) (ifVec g c lhs rhs).2 ∧ (ifVec g c lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,c,[]⟩,
    hg,hl,hr,Nat.zero_le _,hc,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=ifVecState_budget s
  have ho:=(ifVecState s).property
  have hv:=ifVecState_value s
  have hn:=ifVecState_length s
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI
