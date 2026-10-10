import Mathlib
import OAI.Computability.QuantumFactoring.NodeControlEmission

namespace OAI



section
namespace ExactQuantumFactoring.NodeStateEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma width (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeStateCircuit.width (s x) (w x)):=
  ((NodeControlEmission.stackWidth hs hw).unaryAdd (NodeControlEmission.stackWidth hs hw)).unarySucc
lemma inWidth (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeStateCircuit.inWidth (s x) (w x)):=
  (width hs hw).unaryAdd hw
lemma pending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.pending (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (const _ _ 0) _ (by intros;simp only [Function.comp_apply,Fin.val_castAdd,Nat.zero_add])
lemma output (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.output (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (NodeControlEmission.stackWidth hs hw).unaryNat _ (by intros;rfl)
lemma bad (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.bad (s x) (w x)):=
  right ((NodeControlEmission.stackWidth hs hw).unaryAdd (NodeControlEmission.stackWidth hs hw)) (const _ _ 1)
lemma top (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.top (s x) (w x)):=
  (pending hs hw).comp (blockNet hs.unarySucc hw (fun _=>0) (const _ _ 0))
lemma old (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.old (s x) (w x)):=left (width hs hw) hw
lemma supplied (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.supplied (s x) (w x)):=right (width hs hw) hw
lemma nodeInput (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nodeInput (s x) (w x)):=
  ((old hs hw).comp (pending hs hw)).pair (supplied hs hw)
lemma nextPending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextPending (s x) (w x)):=
  (nodeInput hs hw).comp (NodeControlEmission.next hs hw)
lemma emission (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.emission (s x) (w x)):=
  (nodeInput hs hw).comp (NodeControlEmission.emitted hs hw)
lemma nextOutput (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextOutput (s x) (w x)):=
  (zeroWord (inWidth hs hw) hw (emission hs hw)).wordMux ((old hs hw).comp (output hs hw))
    (stackPush (inWidth hs hw) hs.unarySucc hw (emission hs hw) ((old hs hw).comp (output hs hw))) (NodeControlEmission.stackWidth hs hw)
lemma nextBad (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextBad (s x) (w x)):=
  ((old hs hw).comp (bad hs hw)).bor ((nodeInput hs hw).comp (NodeControlEmission.failed hs hw))
lemma step (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.step (s x) (w x)):=
  ((nextPending hs hw).pair (nextOutput hs hw)).pair (nextBad hs hw)
end ExactQuantumFactoring.NodeStateEmission

end



end OAI
