import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGMul
import OAI.Computability.QuantumFactoring.NativeAIGVectorBounds

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def MulOK (s : AddData) : Prop:=AddOK s ∧ s.lhs.length=s.rhs.length ∧ s.output.length=s.lhs.length
abbrev MulState:={s : AddData // MulOK s}
def mulStateCode (s : MulState) : List Bool:=addDataCode s.val

def mulStepData (s : AddData) : AddData:=
  let next:=if isZero s.graph ((s.rhs.drop s.curr).headD (0,false)) then (s.graph,s.output) else
    let added:=add s.graph s.output (shift s.lhs s.curr)
    ifVec added.1 ((s.rhs.drop s.curr).headD (0,false)) added.2 s.output
  ⟨s.budget+16*s.lhs.length+1,next.1,s.lhs,s.rhs,s.curr+1,s.cin,next.2⟩
lemma mulStep_ok (s : MulState) : MulOK (mulStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,ha⟩:=s.property
  have hb : s.val.budget ≤ s.val.budget+16*s.val.lhs.length+1:=by omega
  unfold MulOK AddOK mulStepData
  split
  · exact ⟨⟨hg.mono hb,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,ho.mono hb⟩,he,ha⟩
  · have had:=add_bound hg ho (shift_refs hl s.val.curr) (by rw [shift_length];exact ha)
    have hn : s.val.budget+13*s.val.output.length+3*(add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2.length ≤
        s.val.budget+16*s.val.lhs.length+1:=by rw [had.2.2,ha];omega
    have hh:=ifVec_bound had.1 had.2.1 (ho.mono (by omega)) ((hr.get s.val.curr).trans (by omega))
    exact ⟨⟨hh.1.mono hn,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,hh.2.1.mono hn⟩,
      he,hh.2.2.trans (had.2.2.trans ha)⟩
def mulStep (s : MulState) : MulState:=⟨mulStepData s.val,mulStep_ok s⟩
lemma mulStep_budget (s : MulState) : (mulStep s).val.budget=s.val.budget+16*s.val.lhs.length+1 := rfl
lemma mulStep_lhs (s : MulState) : (mulStep s).val.lhs=s.val.lhs := rfl
lemma mulStep_iterate_lhs (s : MulState) (k : ℕ) : ((mulStep^[k]) s).val.lhs=s.val.lhs := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih,mulStep_lhs]
lemma mulStep_iterate_budget (s : MulState) (k : ℕ) :
    ((mulStep^[k]) s).val.budget=s.val.budget+(16*s.val.lhs.length+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,mulStep_budget,mulStep_lhs];ring
lemma mulStep_iterate_loop (s : MulState) (k : ℕ) :
    (((mulStep^[k]) s).val.graph,((mulStep^[k]) s).val.output)=
      mulLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih,mulLoop]
    unfold mulStep mulStepData
    split <;> rfl
lemma mulStateCode_bound (s : MulState) : (mulStateCode s).length ≤ 300*(s.val.budget+1)^2 :=
  addStateCode_bound ⟨s.val,s.property.1⟩
lemma mulBudget_le_code (s : MulState) : s.val.budget ≤ (mulStateCode s).length :=
  budget_le_code ⟨s.val,s.property.1⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI
