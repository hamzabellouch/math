import Mathlib
import OAI.Computability.QuantumFactoring.TreeTableEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma tableFactor {a p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.tableFactor (a x) (p x)):=by
  exact wordMux ((zeroWord hk hn ha).bor (zeroWord hk hn hp)) (wordConst hk hn (const _ _ 2)) hp hn
lemma tableRow {a : ∀x,BooleanNetwork (k x) (n x)} {b : ∀x,BooleanNetwork (k x) (tensorWidth (n x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetsEmits ea (fun x=>List.ofFn (fun i:Fin (n x)=>BitArithmetic.tableFactor (a x) ((b x).comp (ExactQuantumFactoring.tensorSelect (n x) (n x) i)))):=by
  apply NetsEmits.ofFn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact tableFactor (hk.comp hx.snd) hN (ha.compInput hx.snd)
    ((hb.compInput hx.snd).comp (NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat))
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma logGet (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) :
    Emits (fun x:Σa,Fin (((PhysicalTree.machine (n a)).logNets (t a)).length)=>prodCode unaryCode ea (x.2.val,x.1))
      Emission.rowCode (fun x=>let r:=((PhysicalTree.machine (n x.1)).logNets (t x.1)).get x.2
        (erasePack r.1,erasePack r.2)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (((PhysicalTree.machine (n a)).logNets (t a)).length)=>(x.2.val,x.1))
  have h:=(ofProcedure (Procedure.listGet Emission.rowCode (emptyPack,emptyPack))).comp
    (hx.fst.unaryNat.pair ((logNets hn ht).comp hx.snd))
  exact h.congr (by
    intro x
    simp only [packedLog,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,
      List.getElem?_eq_getElem x.2.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem])
lemma tableNets (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetsEmits ea
    (fun x=>BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))):=by
  let L:=fun x=>(PhysicalTree.machine (n x)).logNets (t x)
  have hl : Emits ea unaryCode (fun x=>(L x).length):=ht.congr (fun x=>(NodeMachine.logNets_length ..).symm)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((L a).length)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  have hT:=ht.comp hx.snd
  have hq:=NetEmits.ofCanonical (logGet hn ht).fst
  have hr:=NetEmits.ofCanonical (logGet hn ht).snd
  have hrows:=NetEmits.tableRow (machineWidth hN hT) hN hq hr
  exact (NetsEmits.concat (f:=fun x i=>List.ofFn (fun j:Fin (n x)=>BitArithmetic.tableFactor ((L x).get i).1 (((L x).get i).2.comp (ExactQuantumFactoring.tensorSelect (n x) (n x) j)))) hl hrows).congrList (by
    intro x
    simp only [BitArithmetic.tableNets,NodeMachine.fieldRows,List.flatMap_map,Function.comp_def,List.map_ofFn]
    rw [List.flatMap_def]
    congr 1
    conv_rhs=>rw [←List.ofFn_get ((PhysicalTree.machine (n x)).logNets (t x)),List.map_ofFn]
    rfl)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
