import Mathlib
import OAI.Computability.QuantumFactoring.RootCircuitEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {w K : α→ℕ}
lemma euclidStep (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.euclidStep (w x)):=by
  have hz:=wordConst (hw.unaryAdd hw) hw (const _ _ 0)
  have hd:=(rootGuess hw).equalOn hz hw
  exact (hd.wordMux (rootModulus hw) (rootGuess hw) hw).pair (hd.wordMux hz (mod hw) hw)
lemma euclidPrefix (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K) :
    NetEmits ea (fun x=>BitArithmetic.euclidPrefix (w x) (K x)):=by
  apply ((euclidStep hw).iterate (hw.unaryAdd hw) hK).congr
  intro x
  have h : ∀j,BooleanNetwork.iterate (BitArithmetic.euclidStep (w x)) j=BitArithmetic.euclidPrefix (w x) j:=by
    intro j;induction j with
    | zero=>rfl
    | succ j ih=>simpa only [BooleanNetwork.iterate, List.replicate_succ, BooleanNetwork.sequence, BitArithmetic.euclidPrefix] using congrArg (BooleanNetwork.comp (BitArithmetic.euclidStep (w x))) ih
  exact h _
lemma gcd (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.gcdNet (w x)):=
  (euclidPrefix hw ((const _ _ 2).unaryMul hw)).comp (rootModulus hw)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
