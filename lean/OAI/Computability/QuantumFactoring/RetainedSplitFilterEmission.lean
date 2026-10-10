import Mathlib
import OAI.Computability.QuantumFactoring.RetainedOrderFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma hardOn {k w : α→ℕ} {a : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>UniversalSplit.hardOn (a x)):=
  (((wordConst hk hw (const _ _ 2)).wordLe ha hw).band (ha.comp (primeWord hw)).bnot).band
    ((evenOn hk hw ha).bnot.band (((ha.comp (resize hw (hw.unaryMul hw).unarySucc)).comp (perfectPower hw)).bnot))
lemma listDummyFilter {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).listDummyFilter (t x) (m x) (raw x)):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (listVarWidth hn) hW h2 hd
    (const _ _ (RatExpr.const (v:=Fin 3) 1)) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (listFilterVars hn ht hm hr) (hr.comp (rareWires hq hW h2 hd)) (constant (machineWidth hn ht) (const _ _ true))
    (zeroWord (machineWidth hn ht) hW (hr.comp (guessWires hq hW h2 hd)))
lemma splitActualFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).splitActualFilter (hn0 x) (t x) (raw x)):=by
  have hh:=retainedListFilter hn ht hn0 (hr.comp (PhysicalSplitEmission.modulus hn))
    ((hr.comp (PhysicalSplitEmission.launchWires hn)).comp (PhysicalSplitEmission.listWires hn))
  apply hh.band
  apply allOfFn (machineWidth hn ht) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hr':=hr.compInput hx.snd
  exact retainedOrderFilter hn' (ht.comp hx.snd)
    (hr'.comp (PhysicalSplitEmission.actualBase hn' (fun x=>x.2) hx.fst.unaryNat))
    (hr'.comp (PhysicalSplitEmission.modulus hn'))
    (hr'.comp (PhysicalSplitEmission.actualOrderRaw hn' (fun x=>x.2) hx.fst.unaryNat))
lemma splitDummyFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).splitDummyFilter (t x) (raw x)):=by
  have hh:=listDummyFilter hn ht (hr.comp (PhysicalSplitEmission.modulus hn))
    ((hr.comp (PhysicalSplitEmission.launchWires hn)).comp (PhysicalSplitEmission.listWires hn))
  apply hh.band
  apply allOfFn (machineWidth hn ht) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hr':=hr.compInput hx.snd
  exact orderDummyFilter hn' (ht.comp hx.snd)
    (hr'.comp (PhysicalSplitEmission.actualBase hn' (fun x=>x.2) hx.fst.unaryNat))
    (hr'.comp (PhysicalSplitEmission.modulus hn'))
    (hr'.comp (PhysicalSplitEmission.actualOrderRaw hn' (fun x=>x.2) hx.fst.unaryNat))
lemma retainedSplitFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedSplitFilter (hn0 x) (t x) (raw x)):=by
  have hh:=hardOn (machineWidth hn ht) hn (hr.comp (PhysicalSplitEmission.modulus hn))
  exact (hh.band (splitActualFilter hn ht hn0 hr)).bor (hh.bnot.band (splitDummyFilter hn ht hr))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
