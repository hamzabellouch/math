import Mathlib
import OAI.Computability.QuantumFactoring.NetworkStackCompiler

namespace OAI

section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def combineStackP : Procedure (prodCode boolCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep (.inr x.1) x.2):=by
  let sw:=first boolCode (listCode packCode)
  let s:=second boolCode (listCode packCode)
  let tl:=(listTail (ea:=packCode)).comp s
  let a:=(listHead packCode emptyPack).comp tl
  let b:=(listHead packCode emptyPack).comp s
  let o:=conditional sw (compPackP.comp (a.pair b)) (pairPackP.comp (a.pair b))
  exact ((listCons packCode).comp (o.pair ((listTail (ea:=packCode)).comp tl))).congrFun (by intro x;rfl)
noncomputable def stackStepP : Procedure (prodCode stackOpCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep x.1 x.2):=by
  let o:=first stackOpCode (listCode packCode)
  let s:=second stackOpCode (listCode packCode)
  let tag:=(casesSum (Procedure.constant packCode boolCode false) (Procedure.constant boolCode boolCode true)).comp o
  let p:=(casesSum (identity packCode) (Procedure.constant boolCode packCode emptyPack)).comp o
  let b:=(casesSum (Procedure.constant packCode boolCode false) (identity boolCode)).comp o
  exact (conditional tag (combineStackP.comp (b.pair s)) ((listCons packCode).comp (p.pair s))).congrFun (by
    rintro ⟨o,s⟩;cases o <;> rfl)
noncomputable def stackFoldP : Procedure (prodCode (listCode stackOpCode) (listCode packCode)) (listCode packCode)
    (fun x=>x.1.foldl (fun s o=>stackStep o s) x.2):=
  foldList (.inr false) stackStepP (Polynomial.X*(Polynomial.C 208*(Polynomial.X+1)^2+2)+1) (by
    intro ops s i
    let t:=(ops.take i).foldl (fun s o=>stackStep o s) s
    have hb:=stackFold_budget (ops.take i) s
    have hs:=packBudgets_le_code s
    have ho:=(opWeights_le_code (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hlen:=stackFold_length (ops.take i) s
    have hop:=(list_length_le_code stackOpCode (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hss:=list_length_le_code packCode s
    have hB : stackBudget t+1≤(listCode stackOpCode ops).length+(listCode packCode s).length+1:=by
      change stackBudget s≤_ at hs
      dsimp only [t];omega
    have hL : t.length≤(listCode stackOpCode ops).length+(listCode packCode s).length:=by dsimp only [t];omega
    have hh:=stackCode_bound t
    have hm:=Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.mul_le_mul_left 208 (Nat.pow_le_pow_left hB 2)) 2)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_ofNat]
    exact hh.trans (Nat.add_le_add_right hm 1))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
