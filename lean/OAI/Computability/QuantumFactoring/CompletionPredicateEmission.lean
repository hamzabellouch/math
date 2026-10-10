import Mathlib
import OAI.Computability.QuantumFactoring.CompletionPredicateCircuit
import OAI.Computability.QuantumFactoring.RationalEmission
import OAI.Computability.QuantumFactoring.ProperDivisorEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool} {W t : α→ℕ}
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma ordinaryMass {s : α→RatExpr v} (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) :
    REm (fun x=>Completion.Expressions.ordinaryMass (t x) (s x)):=
  rMul (rConst ((const _ _ 1).ratSub ((const _ _ 1).ratDiv ((const _ _ 2).ratPow ht)))) hs
lemma completionCoefficient {s z : α→RatExpr v} (hW : BitStackProgram.Emits ea unaryCode W)
    (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) (hz : REm z) :
    REm (fun x=>Completion.Expressions.coefficient (W x) (t x) (s x) (z x)):=by
  have h2:=rConst ((const _ _ 2).ratPow ((hW.unaryAdd ht).unaryAdd (const _ _ 2))) (ev:=ev)
  exact rDiv (rOfInt (rFloor (rMul h2 (rDiv hz (ordinaryMass ht hs))))) h2
lemma completionGuess {s z : α→RatExpr v} (hW : BitStackProgram.Emits ea unaryCode W)
    (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) (hz : REm z) :
    REm (fun x=>Completion.Expressions.guess (W x) (t x) (s x) (z x)):=
  rDiv (rMul (rSub hz (rMul (completionCoefficient hW ht hs hz) (ordinaryMass ht hs)))
    (rConst ((const _ _ 2).ratPow hW))) (rConst ((const _ _ 1).ratDiv ((const _ _ 2).ratPow ht)))
end ExactQuantumFactoring.NetworkEmission.Emits
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {k b W t d : α→ℕ}
lemma predicateFilter {K : ℕ} (en : Fin K ≃ v) {s z : α→RatExpr v} {coin : α→NatExpr v}
    {vars : ∀x,v→BooleanNetwork (k x) (b x)} {branch : ∀x,BooleanNetwork (k x) (t x)}
    {good guess : ∀x,BooleanNetwork (k x) 1}
    (hk : Emits ea unaryCode k) (hb : Emits ea unaryCode b) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d)
    (hs : Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) s)
    (hz : Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) z)
    (hc : Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) coin)
    (hv : ∀i,NetEmits ea (fun x=>vars x i)) (hr : NetEmits ea branch)
    (hg : NetEmits ea good) (hgg : NetEmits ea guess) :
    NetEmits ea (fun x=>Completion.predicateFilter (W:=W x) (d x) (s x) (z x) (vars x) (branch x) (coin x) (good x) (guess x)):=by
  have hrare:=zeroWord hk ht hr
  have ho:=retention en hk hb (coinBits hW ht hd) (Emits.completionCoefficient hW ht hs hz) hc hv
  have hguess:=retention en hk hb (coinBits hW ht hd) (Emits.completionGuess hW ht hs hz) hc hv
  exact (hrare.bnot.band (hg.band ho)).bor (hrare.band (hgg.band hguess))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
