import Mathlib
import OAI.Computability.QuantumFactoring.BitStackIteration
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper
import OAI.Computability.QuantumFactoring.NativeAIGZipFold

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def BinBound (C : ℕ) (op : BinOp) : Prop:=∀{B : ℕ} {r : Graph},Bounded B r→∀a b,
  a.1≤B→b.1≤B→Bounded (B+C) (op r a b).1 ∧ (op r a b).2.1≤B+C

def binaryStepData (collect : Bool) (C : ℕ) (op : BinOp) (s : AddData) : AddData:=
  let a:=if collect then (s.lhs.drop s.curr).headD (0,false) else s.cin
  let ss:=op s.graph a ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+C+1,ss.1,s.lhs,s.rhs,s.curr+1,ss.2,if collect then s.output++[ss.2] else s.output⟩
lemma binaryStep_ok (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    AddOK (binaryStepData collect C op s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have ha : (if collect then ((s.val.lhs.drop s.val.curr).headD (0,false)) else s.val.cin).1 ≤ s.val.budget:=by
    cases collect <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> first | exact hci | exact hl.get _
  have hh:=hop hg _ _ ha (hr.get s.val.curr)
  dsimp only [AddOK,binaryStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,hh.2.trans (by omega),?_⟩
  cases collect <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact ho.mono (by omega)
  · refine ⟨by simp only [List.length_append,List.length_singleton];have:=ho.1;omega,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (ho.2 a ha).trans (by omega)
    · have he:=List.mem_singleton.mp ha
      rw [he];exact hh.2.trans (by omega)
def binaryStep (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  ⟨binaryStepData collect C op s.val,binaryStep_ok collect hop s⟩
lemma binaryStep_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (binaryStep collect hop s).val.budget=s.val.budget+C+1:=rfl
lemma binaryStep_iterate_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep collect hop)^[k] s).val.budget=s.val.budget+(C+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,binaryStep_budget];ring
lemma binaryStep_zipLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep true hop)^[k] s).val.graph,((binaryStep true hop)^[k] s).val.output)=
      zipLoop op k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_foldLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep false hop)^[k] s).val.graph,((binaryStep false hop)^[k] s).val.cin)=
      foldLoop op k s.val.graph s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_zipLength {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep true hop)^[k] s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih];simp only [binaryStep,binaryStepData,ite_true,
      List.length_append,List.length_singleton];omega

def zipState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep true hop)^[s.val.lhs.length] (initializeAdd s)
lemma zipState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((zipState hop s).val.graph,(zipState hop s).val.output)=zipVec op s.val.graph s.val.lhs s.val.rhs:=
  binaryStep_zipLoop hop _ _
lemma zipState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.budget=s.val.budget+(C+1)*s.val.lhs.length:=binaryStep_iterate_budget _ _ _ _
lemma zipState_length {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.output.length=s.val.lhs.length:=by
  unfold zipState
  rw [binaryStep_zipLength]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]

def initializeFold (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def foldState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep false hop)^[s.val.rhs.length] (initializeFold s)
lemma foldState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((foldState hop s).val.graph,(foldState hop s).val.cin)=foldVec op s.val.graph s.val.rhs:=
  binaryStep_foldLoop hop _ _
lemma foldState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (foldState hop s).val.budget=s.val.budget+(C+1)*s.val.rhs.length:=binaryStep_iterate_budget _ _ _ _

namespace Emission
noncomputable def binaryStepDataP (collect : Bool) (C : ℕ) {op : BinOp}
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addDataCode addDataCode (binaryStepData collect C op) := by
  let b:=(unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode (C+1))))
  let a:=conditional (Procedure.constant _ boolCode collect)
    ((listGet refCode (0,false)).comp (addCurrP.pair addLhsP)) addCinP
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let ss:=p.comp (addGraphP.pair (a.pair rhs))
  let g:=(first graphCode refCode).comp ss
  let c:=(second graphCode refCode).comp ss
  let out:=conditional (Procedure.constant _ boolCode collect)
    ((listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp c))) addOutputP
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair out))))))).congrFun (by
      intro s;cases collect <;> simp only [binaryStepData,Nat.add_assoc,Function.comp_apply,
        Bool.false_eq_true,ite_true,ite_false,addDataView])
noncomputable def binaryStepP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (binaryStep collect hop):=
  ((binaryStepDataP collect C p).precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def binaryIterationP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode addStateCode) addStateCode (fun x=>(binaryStep collect hop)^[x.1] x.2):=
  (binaryStepP collect hop p).iterate (Polynomial.C (300*(C+1)^2)*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((binaryStep collect hop)^[i] s)
    rw [binaryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hs : s.val.budget+1≤(C+1)*((addStateCode s).length+1):=by nlinarith
    have hn:=Nat.mul_le_mul_left (C+1) hi
    have h : s.val.budget+(C+1)*i+1≤(C+1)*(n+(addStateCode s).length+1):=by nlinarith
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def zipStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (zipState hop):=
  (binaryIterationP true hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def initializeFoldP : Procedure addStateCode addStateCode initializeFold := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def foldStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (foldState hop):=
  (binaryIterationP false hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addRhsP.precompose (fun s:AddState=>s.val))).pair initializeFoldP)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
