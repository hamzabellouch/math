import Mathlib
import OAI.Computability.QuantumFactoring.RetainedListFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma orderRate (hn : Emits ea unaryCode n) : Emits ea (ratExprCode (fun i:Fin 3=>i.val.bits))
    (fun x=>Completion.Expressions.orderRateCoin (n x) (n x^5)):=
  NetworkEmission.Emits.repeatedSuccess
    (NetworkEmission.Emits.rMul (NetworkEmission.Emits.rOfNat (const _ _ (NatExpr.var (1:Fin 3))))
      (NetworkEmission.Emits.lambdaExpr hn (const _ _ (NatExpr.var (0:Fin 3))))) (hn.unaryPow 5)
lemma orderVarWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeMachine.orderVarWidth (n x)):=
  hn.unaryAdd (coinBits (transitionWidth hn) ((const _ _ 2).unaryMul hn) ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)))
lemma orderFilterVars {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) (i : Fin 3) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderFilterVars (t x) (a x) (m x) (raw x) i):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  fin_cases i
  · exact (retainedOrder hn ht ha hm).comp (resize hn (orderVarWidth hn))
  · exact (retainedOrderPhi hn ht ha hm).comp (resize hn (orderVarWidth hn))
  · exact (hr.comp (retentionWires hq hW h2 hd)).comp (resize (coinBits hW h2 hd) (orderVarWidth hn))
lemma orderActualFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderActualFilter (t x) (a x) (m x) (raw x)):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  have ho:=retainedOrder hn ht ha hm
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (orderVarWidth hn) hW h2 hd
    (orderRate hn) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (orderFilterVars hn ht ha hm hr) (hr.comp (rareWires hq hW h2 hd))
    ((PhysicalOrderEmission.result (machineWidth hn ht) hn ha hm (hr.comp (ordinaryWires hq hW h2 hd))).equalOn ho hn)
    ((hr.comp (guessWires hq hW h2 hd)).equalOn (ho.comp (resize hn hW)) hW)
lemma orderDummyFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderDummyFilter (t x) (a x) (m x) (raw x)):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (orderVarWidth hn) hW h2 hd
    (const _ _ (RatExpr.const (v:=Fin 3) 1)) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (orderFilterVars hn ht ha hm hr) (hr.comp (rareWires hq hW h2 hd)) (constant (machineWidth hn ht) (const _ _ true))
    (zeroWord (machineWidth hn ht) hW (hr.comp (guessWires hq hW h2 hd)))
lemma retainedOrderFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrderFilter (t x) (a x) (m x) (raw x)):=by
  have hu:=PhysicalOrderEmission.usable (machineWidth hn ht) hn ha hm
  exact (hu.band (orderActualFilter hn ht ha hm hr)).bor (hu.bnot.band (orderDummyFilter hn ht ha hm hr))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
