import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGMulBounded

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def mulAddInput (s : MulState) : AddState:=
  ⟨⟨s.val.budget,s.val.graph,s.val.output,shift s.val.lhs s.val.curr,0,(0,false),[]⟩,
   s.property.1.1,s.property.1.2.2.2.2.2,shift_refs s.property.1.2.1 _,Nat.zero_le _,Nat.zero_le _,
   Nat.zero_le _,by intro a ha;cases ha⟩
def mulAdded (s : MulState) : AddState:=addState (mulAddInput s)
lemma mulAdded_value (s : MulState) : ((mulAdded s).val.graph,(mulAdded s).val.output)=
    add s.val.graph s.val.output (shift s.val.lhs s.val.curr) :=addState_value _
lemma mulAdded_budget (s : MulState) : (mulAdded s).val.budget=s.val.budget+13*s.val.lhs.length := by
  have hh:=addState_budget_eq (mulAddInput s) (by
    change s.val.output.length=(shift s.val.lhs s.val.curr).length
    rw [shift_length];exact s.property.2.2)
  simpa only [mulAdded,mulAddInput,s.property.2.2] using hh
lemma mulAdded_length (s : MulState) : (mulAdded s).val.output.length=s.val.lhs.length := by
  have hh:=addState_length (mulAddInput s) (by
    change s.val.output.length=(shift s.val.lhs s.val.curr).length
    rw [shift_length];exact s.property.2.2)
  exact hh.trans s.property.2.2

def mulIfInput (s : MulState) : AddState:=
  ⟨⟨(mulAdded s).val.budget,(mulAdded s).val.graph,(mulAdded s).val.output,s.val.output,0,
      (s.val.rhs.drop s.val.curr).headD (0,false),[]⟩,
    (mulAdded s).property.1,(mulAdded s).property.2.2.2.2.2,
    s.property.1.2.2.2.2.2.mono (by rw [mulAdded_budget];omega),Nat.zero_le _,
    (s.property.1.2.2.1.get _).trans (by rw [mulAdded_budget];omega),Nat.zero_le _,by intro a ha;cases ha⟩
lemma mulIfInput_value (s : MulState) :
    ifVec (mulIfInput s).val.graph (mulIfInput s).val.cin (mulIfInput s).val.lhs (mulIfInput s).val.rhs=
      ifVec (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).1
        ((s.val.rhs.drop s.val.curr).headD (0,false))
        (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2 s.val.output := by
  have hh:=mulAdded_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [mulIfInput]
  rw [h1,h2]

namespace Emission
noncomputable def mulBudgetP : Procedure mulStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:MulState=>s.val)
noncomputable def mulGraphP : Procedure mulStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:MulState=>s.val)
noncomputable def mulLhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.lhs):=
  addLhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulRhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.rhs):=
  addRhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulOutputP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:MulState=>s.val)
noncomputable def mulCurrP : Procedure mulStateCode Nat.bits (fun s=>s.val.curr):=
  addCurrP.precompose (fun s:MulState=>s.val)
noncomputable def mulCinP : Procedure mulStateCode refCode (fun s=>s.val.cin):=
  addCinP.precompose (fun s:MulState=>s.val)
noncomputable def mulAddInputP : Procedure mulStateCode addStateCode mulAddInput := by
  let sh:=shiftP.comp (mulLhsP.pair mulCurrP)
  exact (packAddP.comp (mulBudgetP.pair (mulGraphP.pair (mulOutputP.pair (sh.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
    (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def mulAddedP : Procedure mulStateCode addStateCode mulAdded :=addStateP.comp mulAddInputP
noncomputable def mulIfInputP : Procedure mulStateCode addStateCode mulIfInput := by
  let ad:=mulAddedP
  let budget:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ad
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ad
  let added:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ad
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  exact (packAddP.comp (budget.pair (g.pair (added.pair (mulOutputP.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def isZeroP : Procedure (prodCode graphCode refCode) boolCode (fun x=>isZero x.1 x.2):=by
  let inv := (second Nat.bits boolCode).comp (second graphCode refCode)
  exact (boolAnd.comp (knownP.pair (boolNot.comp inv))).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
    unfold known isZero constant
    cases g.decls[i]?.getD Decl.zero <;> cases b <;> rfl)
noncomputable def mulNextP : Procedure mulStateCode (prodCode graphCode (listCode refCode))
    (fun s=>if isZero s.val.graph ((s.val.rhs.drop s.val.curr).headD (0,false)) then (s.val.graph,s.val.output)
      else let added:=add s.val.graph s.val.output (shift s.val.lhs s.val.curr)
        ifVec added.1 ((s.val.rhs.drop s.val.curr).headD (0,false)) added.2 s.val.output) := by
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  let test:=isZeroP.comp (mulGraphP.pair c)
  let no:=(ifVecP.comp mulIfInputP).congrFun mulIfInput_value
  exact conditional test (mulGraphP.pair mulOutputP) no
noncomputable def mulStepP : Procedure mulStateCode mulStateCode mulStep := by
  let len:=(listUnaryLength refCode (0,false)).comp mulLhsP
  let cost:=unaryMul.comp ((Procedure.constant _ unaryCode 16).pair len)
  let b:=unarySuccessor.comp (unaryAdd.comp (mulBudgetP.pair cost))
  let g:=(first graphCode (listCode refCode)).comp mulNextP
  let out:=(second graphCode (listCode refCode)).comp mulNextP
  exact (packAddP.comp (b.pair (g.pair (mulLhsP.pair (mulRhsP.pair
    ((successor.comp mulCurrP).pair (mulCinP.pair out))))))).result (by intro s;rfl)
noncomputable def mulIterationP : Procedure (prodCode unaryCode mulStateCode) mulStateCode
    (fun x=>(mulStep^[x.1]) x.2) :=
  mulStepP.iterate (Polynomial.C 97200*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=mulStateCode_bound ((mulStep^[i]) s)
    rw [mulStep_iterate_budget] at hh
    have hb:=mulBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(mulStateCode s).length+1
    have hM : 1 ≤ M:=by dsimp [M];omega
    have hB : s.val.budget+1 ≤ M:=by dsimp [M];omega
    have hw : 16*s.val.lhs.length+1 ≤ 17*M:=by omega
    have hii : i ≤ M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.budget+(16*s.val.lhs.length+1)*i+1 ≤ 18*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (mulStateCode ((mulStep^[i]) s)).length ≤ 300*(s.val.budget+(16*s.val.lhs.length+1)*i+1)^2:=hh
      _ ≤ 300*(18*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 97200*(n+(mulStateCode s).length+1)^4:=by dsimp [M];ring)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
