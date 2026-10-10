import Mathlib
import OAI.Computability.QuantumFactoring.RetainedArithmeticEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma favorableComparison {a m p : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BooleanNetwork.all ((BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))).map
      (fun q=>(BitArithmetic.dividesOn (p x) (m x)).bnot.bor ((BitArithmetic.dividesOn q (m x)).bnot.bor
        (BitArithmetic.sameTwoVal ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x))
          ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))))):=by
  have hps:=tableNets hn ht
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((BitArithmetic.tableNets ((PhysicalTree.machine (n a)).fieldRows (t a))).length)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have ht':=ht.comp hx.snd
  have ha':=ha.compInput hx.snd
  have hm':=hm.compInput hx.snd
  have hp':=hp.compInput hx.snd
  have hk:=machineWidth hn' ht'
  have hc:=(dividesOn hk hn' hp' hm').bnot.bor ((dividesOn hk hn' hps.get hm').bnot.bor
    (sameTwoVal hk hn' (retainedComponentOrder hn' ht' ha' hm' hp') (retainedComponentOrder hn' ht' ha' hm' hps.get)))
  exact (hps.map (g:=fun x q=>(BitArithmetic.dividesOn (p x) (m x)).bnot.bor
    ((BitArithmetic.dividesOn q (m x)).bnot.bor (BitArithmetic.sameTwoVal
    ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x))
    ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))) hc).all (machineWidth hn ht)
lemma retainedFavorable {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedFavorable (t x) (a x) (m x)):=by
  have hps:=tableNets hn ht
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((BitArithmetic.tableNets ((PhysicalTree.machine (n a)).fieldRows (t a))).length)=>(x.2.val,x.1))
  have hc:=favorableComparison (hn.comp hx.snd) (ht.comp hx.snd) (ha.compInput hx.snd) (hm.compInput hx.snd) hps.get
  exact (PhysicalOrderEmission.usable (machineWidth hn ht) hn ha hm).band ((hps.map
    (g:=fun x p=>BooleanNetwork.all ((BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))).map
      (fun q=>(BitArithmetic.dividesOn p (m x)).bnot.bor ((BitArithmetic.dividesOn q (m x)).bnot.bor
        (BitArithmetic.sameTwoVal ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) p)
          ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))))) hc).all (machineWidth hn ht)).bnot
lemma retainedGoodList {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x*(n x^5+1))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedGoodList (t x) (m x) (y x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  exact anyOfFn (machineWidth hn ht) (hn.unaryPow 5) (retainedFavorable (hn.comp hx.snd) (ht.comp hx.snd)
    (transitionRead (hn.comp hx.snd) (hy.compInput hx.snd) (fun x=>x.2) hx.fst.unaryNat) (hm.compInput hx.snd))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
