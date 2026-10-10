import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionTokenProcedure
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
def tokenMap (f : v→ℕ) : ExprToken v→ExprToken ℕ:=Sum.map f id
lemma tokenMap_code (f : v→ℕ) (t : ExprToken v) :
    exprTokenCode Nat.bits (tokenMap f t)=exprTokenCode (fun i=>(f i).bits) t:=by
  rcases t with i|c|j <;> rfl
lemma tokenMap_listCode (f : v→ℕ) (ts : List (ExprToken v)) :
    listCode (exprTokenCode Nat.bits) (ts.map (tokenMap f))=
    listCode (exprTokenCode (fun i=>(f i).bits)) ts:=by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>simp only [List.map_cons,listCode,tokenMap_code,ih]
lemma tokenMap_op (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (t : ExprToken v) :
    tokenOp n w vs (tokenMap f t)=tokenOp n w (fun i=>vs (f i)) t:=by
  rcases t with i|c|j
  · rfl
  · rfl
  · rcases j with _|j <;> try rfl
    rcases j with _|j <;> rfl
lemma tokenMap_run (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (ts : List (ExprToken v)) (s : List Pack) :
    exprRun n w vs (ts.map (tokenMap f)) s=exprRun n w (fun i=>vs (f i)) ts s:=by
  simp only [exprRun,List.map_map,Function.comp_def,tokenMap_op]
namespace Emission
noncomputable def genericExprResultP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (listCode (exprTokenCode (fun i=>(f i).bits)))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2 []).headD emptyPack):=by
  let p:=exprResultP.precompose (fun x : ExprEnv×List (ExprToken v)=>(x.1,x.2.map (tokenMap f)))
  exact (p.congrEncoding (by intro x;dsimp only [prodCode];rw [tokenMap_listCode]) (by intro x;rfl)).congrFun (by
    intro x;dsimp only [Function.comp_apply];rw [tokenMap_run])
noncomputable def genericExprPackP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (exprCode (fun i=>(f i).bits))) packCode
    (fun x=>exprPack x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2):=
  ((genericExprResultP f).comp ((first _ _).pair ((exprTokensP _).comp (second _ _)))).congrFun (by
    intro x;change (exprRun _ _ _ (exprTokens x.2) []).headD emptyPack=_
    rw [exprTokens_produces];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
