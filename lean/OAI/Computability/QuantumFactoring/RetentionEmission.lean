import Mathlib
import OAI.Computability.QuantumFactoring.RetentionCircuit
import OAI.Computability.QuantumFactoring.BitStackPowers
import OAI.Computability.QuantumFactoring.ArithmeticSyntaxEmission
import OAI.Computability.QuantumFactoring.NetworkFiniteExpressionEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma threshold {T : α→ℕ} {p : α→RatExpr v} {coin : α→NatExpr v}
    (hT : BitStackProgram.Emits ea unaryCode T)
    (hp : BitStackProgram.Emits ea (ratExprCode ev) p)
    (hc : BitStackProgram.Emits ea (exprCode ev) coin) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>thresholdExpr (T x) (p x) (coin x)):=by
  have ht : BitStackProgram.Emits ea Nat.bits (fun x=>2^(T x)):=
    (ofProcedure Procedure.binaryPow).comp (hT.pair (const _ _ 2))
  exact nite (nadd hc (const _ _ (NatExpr.const (v:=v) 1)))
    (iToNat (rFloor (rMul hp (rOfNat (nconst ht))))) (const _ _ (NatExpr.const (v:=v) 1)) (const _ _ (NatExpr.const (v:=v) 0))
end Emits
namespace NetEmits
variable {α v : Type} {ea : α→List Bool} {n b T : α→ℕ}
lemma retention {k : ℕ} (en : Fin k ≃ v) {p : α→RatExpr v} {coin : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    (hT : BitStackProgram.Emits ea unaryCode T)
    (hp : BitStackProgram.Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) p)
    (hc : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) coin)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>retentionNet (T x) (p x) (coin x) (fs x)):=
  isOneFinite en (Emits.threshold hT hp hc) hn hb hf
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
