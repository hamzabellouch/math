import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionPostfix
import OAI.Computability.QuantumFactoring.BitStackSumInjection
import OAI.Computability.QuantumFactoring.EmissionFurther

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure AIGNetworkEmission
namespace Emission
noncomputable def primPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>primPack x.1 x.2):=by
  let w:=first unaryCode Nat.bits
  let j:=second unaryCode Nat.bits
  let eq (i:ℕ):=binaryEq.comp (j.pair (Procedure.constant _ Nat.bits i))
  let a:=AIGNetworkEmission.Emission.addPackP.comp w
  let b:=AIGNetworkEmission.Emission.mulPackP.comp w
  let c:=AIGNetworkEmission.Emission.subPackP.comp w
  let d:=AIGNetworkEmission.Emission.divPackP.comp w
  let e:=AIGNetworkEmission.Emission.modPackP.comp w
  let f:=AIGNetworkEmission.Emission.ultPackP.comp w
  let g:=Procedure.constant (prodCode unaryCode Nat.bits) packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))
  let h:=muxVectorPackP.comp w
  exact (conditional (eq 0) a (conditional (eq 1) b (conditional (eq 2) c (conditional (eq 3) d
    (conditional (eq 4) e (conditional (eq 5) f (conditional (eq 6) g h))))))).congrFun (by
    rintro ⟨w,j⟩
    rcases j with _|j <;> simp only [Function.comp_apply,decide_eq_true_eq,primPack]
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    simp)

def tokenTag : ExprToken ℕ→ℕ | .inl _=>0 | .inr (.inl _)=>1 | .inr (.inr _)=>2
def tokenPayload : ExprToken ℕ→ℕ | .inl i=>i | .inr (.inl c)=>c | .inr (.inr j)=>j
noncomputable def tokenTagP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenTag:=
  (casesSum (Procedure.constant Nat.bits Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant Nat.bits Nat.bits 2))).congrFun (by
      intro t;rcases t with i|c|j <;> rfl)
noncomputable def tokenPayloadP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenPayload:=
  (casesSum (identity Nat.bits) (casesSum (identity Nat.bits) (identity Nat.bits))).congrFun (by
    intro t;rcases t with i|c|j <;> rfl)
abbrev exprEnvCode:=prodCode unaryCode (prodCode unaryCode (listCode packCode))
abbrev ExprEnv:=ℕ×ℕ×List Pack
def envVars (xs : List Pack) (i : ℕ) : Pack:=(xs.drop i).headD emptyPack
noncomputable def tokenOpP : Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) stackOpCode
    (fun x=>tokenOp x.1.1 x.1.2.1 (envVars x.1.2.2) x.2):=by
  let env:=first exprEnvCode (exprTokenCode Nat.bits)
  let n:=(first unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let rest:=(second unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let w:=(first unaryCode (listCode packCode)).comp rest
  let vs:=(second unaryCode (listCode packCode)).comp rest
  let tok:=second exprEnvCode (exprTokenCode Nat.bits)
  let tag:=tokenTagP.comp tok
  let val:=tokenPayloadP.comp tok
  let eq (i:ℕ) (p:Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) Nat.bits (fun x=>i)):=
    binaryEq.comp (tag.pair p)
  let v:=(sumLeft packCode boolCode).comp ((listGet packCode emptyPack).comp (val.pair vs))
  let c:=(sumLeft packCode boolCode).comp (wordConstPackP.comp (n.pair (w.pair val)))
  let op:=(sumLeft packCode boolCode).comp (primPackP.comp (w.pair (binarySub.comp (val.pair (Procedure.constant _ Nat.bits 2)))))
  let inst:=conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 0)))
    (Procedure.constant _ stackOpCode (.inr false))
    (conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 1))) (Procedure.constant _ stackOpCode (.inr true)) op)
  exact (conditional (eq 0 (Procedure.constant _ Nat.bits 0)) v
    (conditional (eq 1 (Procedure.constant _ Nat.bits 1)) c inst)).congrFun (by
      rintro ⟨⟨n,w,vs⟩,t⟩
      rcases t with i|c|j
      · rfl
      · rfl
      rcases j with _|j
      · rfl
      rcases j with _|j
      · rfl
      simp only [Function.comp_apply,tokenTag,tokenPayload,tokenOp,decide_eq_true_eq,
        Nat.add_one_ne_zero,↓reduceIte]
      rfl)
noncomputable def exprRunP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) (listCode packCode)
    (fun x=>exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []):=by
  let ops:=listMapWith (f:=fun (env : ExprEnv) t=>tokenOp env.1 env.2.1 (envVars env.2.2) t) (Sum.inl 0) (Sum.inr false) tokenOpP
  let start:=(ops.pair (Procedure.constant _ (listCode packCode) []))
  exact stackFoldP.comp start
noncomputable def exprResultP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []).headD emptyPack):=
  (listHead packCode emptyPack).comp exprRunP
/-- Compiler runs in polynomial time in the expanded source syntax, dimensions
and input networks. The environment contains no circuit-generation oracle. -/
noncomputable def exprPackP : Procedure
    (fun x : ExprEnv×NatExpr ℕ=>prodCode exprEnvCode (listCode (exprTokenCode Nat.bits)) (x.1,exprTokens x.2)) packCode
    (fun x=>exprPack x.1.1 x.1.2.1 (envVars x.1.2.2) x.2):=
  (exprResultP.precompose (fun x : ExprEnv×NatExpr ℕ=>(x.1,exprTokens x.2))).congrFun (by
    intro x
    change (exprRun _ _ _ (exprTokens x.2) []).headD emptyPack=_
    rw [exprTokens_produces];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
