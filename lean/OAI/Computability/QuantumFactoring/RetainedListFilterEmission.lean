import Mathlib
import OAI.Computability.QuantumFactoring.RetainedFavorableEmission
import OAI.Computability.QuantumFactoring.CompletionPredicateEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma localTarget (hn : Emits ea unaryCode n) : Emits ea ratCode (fun x=>Completion.target (n x)):=
  (const _ _ 1).ratSub ((const _ _ 1).ratDiv ((const _ _ 2).ratPow hn))
lemma listRate (hn : Emits ea unaryCode n) : Emits ea (ratExprCode (fun i:Fin 3=>i.val.bits))
    (fun x=>Completion.Expressions.listRateCoin (n x) (n x^5)):=by
  exact NetworkEmission.Emits.repeatedSuccess
    (NetworkEmission.Emits.rDiv (NetworkEmission.Emits.rOfNat (const _ _ (NatExpr.var (1:Fin 3))))
      (NetworkEmission.Emits.rOfNat (NetworkEmission.Emits.coveringPow (const _ _ (NatExpr.var (0:Fin 3))) hn))) (hn.unaryPow 5)
lemma listVarWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeMachine.listVarWidth (n x)):=
  hn.unaryAdd (coinBits (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5)))
lemma listFilterVars {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hr : NetEmits ea raw) (i : Fin 3) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).listFilterVars (t x) (m x) (raw x) i):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  fin_cases i
  · exact hm.comp (resize hn (listVarWidth hn))
  · exact (retainedFavorableCount hn ht hm).comp (resize hn (listVarWidth hn))
  · exact (hr.comp (retentionWires hq hW h2 hd)).comp (resize (coinBits hW h2 hd) (listVarWidth hn))
lemma retainedListFilter {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x)
    (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedListFilter (hn0 x) (t x) (m x) (raw x)):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (listVarWidth hn) hW h2 hd
    (listRate hn) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (listFilterVars hn ht hm hr) (hr.comp (rareWires hq hW h2 hd))
    (retainedGoodList hn ht hm ((hr.comp (ordinaryWires hq hW h2 hd)).comp (PhysicalListEmission.ordinary hn)))
    (retainedCanonicalList hn ht hn0 hm (hr.comp (guessWires hq hW h2 hd)))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
