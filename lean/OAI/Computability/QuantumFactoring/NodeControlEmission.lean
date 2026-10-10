import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialFieldsEmission
import OAI.Computability.QuantumFactoring.ProperDivisorEmission
import OAI.Computability.QuantumFactoring.StackEmission

namespace OAI



section
namespace ExactQuantumFactoring.NodeControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
open BitArithmetic.NodeCircuit
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma stackWidth (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>(s x+1)*w x):=hs.unarySucc.unaryMul hw
lemma width (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeCircuit.width (s x) (w x)):=
  (stackWidth hs hw).unaryAdd hw
lemma pending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.pending (s x) (w x)):=left (stackWidth hs hw) hw
lemma divisor (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.divisor (s x) (w x)):=right (stackWidth hs hw) hw
lemma top (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.top (s x) (w x)):=
  (pending hs hw).comp (blockNet hs.unarySucc hw (fun _=>0) (const _ _ 0))
lemma popped (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.popped (s x) (w x)):=
  (pending hs hw).comp (stackPop hs.unarySucc hw)
lemma quotient (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.quotient (s x) (w x)):=
  ((top hs hw).pair (divisor hs hw)).comp (div hw)
lemma isPrime (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isPrime (s x) (w x)):=
  (top hs hw).comp (primeWord hw)
lemma isDone (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isDone (s x) (w x)):=
  zeroWord (width hs hw) hw (top hs hw)
lemma isProper (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isProper (s x) (w x)):=
  properOn (width hs hw) hw (top hs hw) (divisor hs hw)
lemma split (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.split (s x) (w x)):=
  stackPush (width hs hw) hs.unarySucc hw (divisor hs hw)
    (stackPush (width hs hw) hs.unarySucc hw (quotient hs hw) (popped hs hw))
lemma next (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.next (s x) (w x)):=
  (isDone hs hw).wordMux (pending hs hw) ((isPrime hs hw).wordMux (popped hs hw)
    ((isProper hs hw).wordMux (split hs hw) (pending hs hw) (stackWidth hs hw)) (stackWidth hs hw)) (stackWidth hs hw)
lemma emitted (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.emitted (s x) (w x)):=by
  exact (isPrime hs hw).wordMux (top hs hw) (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst (width hs hw) hw (const _ _ 0)) hw
lemma failed (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.failed (s x) (w x)):=
  ((isDone hs hw).bnot.band (isPrime hs hw).bnot).band (isProper hs hw).bnot
end ExactQuantumFactoring.NodeControlEmission

end



end OAI
