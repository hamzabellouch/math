import Mathlib
import OAI.Computability.QuantumFactoring.RetentionCircuit
import OAI.Computability.QuantumFactoring.CoveringPowerEmission
import OAI.Computability.QuantumFactoring.MajorantTemplateEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma powTwo {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) :
    BitStackProgram.Emits ea Nat.bits (fun x=>2^(n x)):=
  (ofProcedure Procedure.binaryPow).comp (hn.pair (const _ _ 2))
lemma lambdaExpr {n : α→ℕ} {d : α→NatExpr v} (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) :
    REm (fun x=>lambdaE (n x) (d x)):=by
  have h:=coveringPow hd hn
  unfold lambdaE;rat_emit
lemma coefficientExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>coefficientE (n x) (Q x) (B x) (d x) (j x)):=by
  have hN:=nconst (ev:=ev) (powTwo ((const _ _ 10).unaryMul hn))
  have hl:=lambdaExpr hn hd
  have hm:=majorantSumExpr hQ hB hd hj
  unfold coefficientE;rat_emit
lemma remainderExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>remainderE (n x) (Q x) (B x) (d x) (j x)):=
  rSub (lambdaExpr hn hd) (rMul (coefficientExpr hn hQ hB hd hj) (majorantSumExpr hQ hB hd hj))
lemma discrepancyExpr {n : α→ℕ} {Q B d j t : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>discrepancyE (n x) (Q x) (B x) (d x) (j x) (t x)):=by
  have hm:=majorantExpr hQ hB hd hj (nmod (nmul hj ht) hd)
  have hp:=probabilityE hQ hd hj ht
  have hc:=coefficientExpr hn hQ hB hd hj
  unfold discrepancyE;rat_emit
lemma thirdRetentionExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>thirdRetentionE (n x) (Q x) (B x) (d x) (j x)):=by
  have hr:=remainderExpr hn hQ hB hd hj
  unfold thirdRetentionE;rat_emit
lemma sampleB {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) : NEm (fun x=>.const (2^(n x))):=
  nconst (powTwo hn)
lemma sampleQ {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) : NEm (fun x=>.const ((2^(n x))^16)):=by
  have h:=(ofProcedure Procedure.binaryPow).comp ((const ea unaryCode 16).pair (powTwo hn))
  exact nconst h
lemma firstExpr {n : α→ℕ} {d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>firstE (n x) (d x) (j x)):=coefficientExpr hn (sampleQ hn) (sampleB hn) hd hj
lemma secondExpr {n : α→ℕ} {d j t : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>secondE (n x) (d x) (j x) (t x)):=discrepancyExpr hn (sampleQ hn) (sampleB hn) hd hj ht
lemma lastExpr {n : α→ℕ} {d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>lastE (n x) (d x) (j x)):=thirdRetentionExpr hn (sampleQ hn) (sampleB hn) hd hj
end ExactQuantumFactoring.NetworkEmission.Emits

end



end OAI
