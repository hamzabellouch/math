import Mathlib
import OAI.Computability.QuantumFactoring.TableNetsEmission
import OAI.Computability.QuantumFactoring.TableFavorableEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma bxor {a b : ∀x,BooleanNetwork (k x) 1} (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>(a x).bxor (b x)):=
  (ha.band hb.bnot).bor (ha.bnot.band hb)
lemma sameTwoVal {a b : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.sameTwoVal (a x) (b x)):=by
  apply allOfFn hk hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hd:=divides (hn.comp hx.snd) (Emits.powTwo hx.fst)
  exact (((ha.compInput hx.snd).comp hd).bxor ((hb.compInput hx.snd).comp hd)).bnot
lemma transitionRead {K : α→ℕ} {y : ∀x,BooleanNetwork (k x) (n x*(K x+1))}
    (hn : Emits ea unaryCode n) (hy : NetEmits ea y) (i : ∀x,Fin (K x))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>TransitionWords.readNet (y x) (i x)):=by
  exact hy.rewireSlice hn (hi.natMul hn.unaryNat) _ (by intro x j; change j.val+n x*(i x).val=(i x).val*n x+j.val; ac_rfl)
lemma transitionFirstOnly {K : α→ℕ} {a : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>TransitionWords.firstOnly (K:=K x) (a x)):=by
  apply transitionEncode hk hn hK
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (K a)=>(x.2.val,x.1))
  exact (ite (hx.fst.unaryNat.natEq (const _ _ 0)) (ha.compInput hx.snd)
    (wordConst (hk.comp hx.snd) (hn.comp hx.snd) (const _ _ 0))).congr (by
      intro x;simp only [decide_eq_true_eq])
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma retainedOrder {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrder (t x) (a x) (m x)):=
  NetEmits.tableOrder (machineWidth hn ht) hn ha hm (tableNets hn ht)
lemma retainedTotient {v : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedTotient (t x) (v x)):=
  NetEmits.tableTotient (machineWidth hn ht) hn hv (tableNets hn ht)
lemma retainedOrderPhi {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrderPhi (t x) (a x) (m x)):=
  retainedTotient hn ht (retainedOrder hn ht ha hm)
lemma retainedComponentOrder {a m p : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x)):=
  retainedOrder hn ht ha (primeComponent (machineWidth hn ht) hn hm hp)
lemma retainedFavorableCount {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedFavorableCount (t x) (m x)):=
  tableFavorableCount (machineWidth hn ht) hn hm (tableNets hn ht)
lemma retainedCanonical {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedCanonical (t x) (a x) (m x)):=
  NetEmits.tableCanonical (machineWidth hn ht) hn (tableNets hn ht) ha hm
lemma retainedCanonicalList {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x*(n x^5+1))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hm : NetEmits ea m) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedCanonicalList (hn0 x) (t x) (m x) (y x)):=by
  have ha:=transitionRead hn hy (fun x=>⟨0,pow_pos (hn0 x) 5⟩) (const _ _ 0)
  exact (retainedCanonical hn ht ha hm).band (hy.equalOn (transitionFirstOnly (machineWidth hn ht) hn (hn.unaryPow 5) ha)
    (transitionWidth hn))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
