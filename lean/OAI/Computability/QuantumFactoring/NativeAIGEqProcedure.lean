import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGZipFoldProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma eqGate_bound : BinBound 3 eqGate:=fun h a b ha hb=>xorGate_bound h a (notRef b) ha hb
lemma andGate_bound : BinBound 1 gate:=fun h a b ha hb=>gate_bound h a b ha hb
lemma zipVec_bound {C B : ℕ} {op : BinOp} (hop : BinBound C op) {r : Graph} {lhs rhs : List Ref}
    (hg : Bounded B r) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+(C+1)*lhs.length) (zipVec op r lhs rhs).1 ∧
    RefsBound (B+(C+1)*lhs.length) (zipVec op r lhs rhs).2 ∧
    (zipVec op r lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,r,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=zipState_budget hop s
  have ho:=(zipState hop s).property
  rw [←zipState_value hop s]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,zipState_length hop s⟩
lemma foldVec_bound {C B : ℕ} {op : BinOp} (hop : BinBound C op) {r : Graph} {xs : List Ref}
    (hg : Bounded B r) (hx : RefsBound B xs) :
    Bounded (B+(C+1)*xs.length) (foldVec op r xs).1 ∧
    (foldVec op r xs).2.1≤B+(C+1)*xs.length := by
  let s : AddState:=⟨⟨B,r,xs,xs,0,(0,false),[]⟩,
    hg,hx,hx,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=foldState_budget hop s
  have ho:=(foldState hop s).property
  rw [←foldState_value hop s]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.1⟩
lemma eqVec_bound {B : ℕ} {r : Graph} {lhs rhs : List Ref}
    (hg : Bounded B r) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+6*lhs.length) (eqVec r lhs rhs).1 ∧ (eqVec r lhs rhs).2.1≤B+6*lhs.length := by
  have hz:=zipVec_bound eqGate_bound hg hl hr
  have hf:=foldVec_bound andGate_bound hz.1 hz.2.1
  rw [hz.2.2] at hf
  have he : B+(3+1)*lhs.length+(1+1)*lhs.length=B+6*lhs.length:=by omega
  simpa only [he,eqVec] using hf

def eqNext (s : AddState) : AddState:=
  let z:=zipState eqGate_bound s
  ⟨⟨z.val.budget,z.val.graph,z.val.output,z.val.output,0,(0,true),[]⟩,
  z.property.1,z.property.2.2.2.2.2,z.property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,
    Nat.zero_le _,by intro a ha;cases ha⟩
def eqState (s : AddState) : AddState:=foldState andGate_bound (eqNext s)
lemma eqState_value (s : AddState) : ((eqState s).val.graph,(eqState s).val.cin)=
    eqVec s.val.graph s.val.lhs s.val.rhs := by
  have hf:=foldState_value andGate_bound (eqNext s)
  change _=foldVec gate (zipState eqGate_bound s).val.graph (zipState eqGate_bound s).val.output at hf
  rw [show (zipState eqGate_bound s).val.graph=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).1 from
    congrArg Prod.fst (zipState_value eqGate_bound s),
    show (zipState eqGate_bound s).val.output=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).2 from
    congrArg Prod.snd (zipState_value eqGate_bound s)] at hf
  exact hf
lemma eqState_budget (s : AddState) : (eqState s).val.budget=s.val.budget+6*s.val.lhs.length := by
  rw [eqState,foldState_budget]
  change (zipState eqGate_bound s).val.budget+(1+1)*(zipState eqGate_bound s).val.output.length=_
  rw [zipState_budget,zipState_length];omega
namespace Emission
noncomputable def eqGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>eqGate x.1 x.2.1 x.2.2):=
  (xorP.comp ((first graphCode keyCode).pair
    ((((first refCode refCode).comp (second graphCode keyCode))).pair
      (notRefP.comp ((second refCode refCode).comp (second graphCode keyCode)))))).congrFun (by intro x;rfl)
noncomputable def eqNextP : Procedure addStateCode addStateCode eqNext := by
  let zp:=zipStateP eqGate_bound eqGateP
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp zp
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp zp
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp zp
  exact (packAddP.comp (b.pair (g.pair (out.pair (out.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def eqStateP : Procedure addStateCode addStateCode eqState:=
  (foldStateP andGate_bound gateP).comp eqNextP
noncomputable def eqP : Procedure addStateCode (prodCode graphCode refCode)
    (fun s=>eqVec s.val.graph s.val.lhs s.val.rhs):=
  (((addGraphP.pair addCinP).precompose (fun s:AddState=>s.val)).comp eqStateP).congrFun eqState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
