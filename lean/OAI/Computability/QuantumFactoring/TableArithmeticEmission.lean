import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTableOrder
import OAI.Computability.QuantumFactoring.PrimeComponentCircuit
import OAI.Computability.QuantumFactoring.TableScanEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {k n w : α→ℕ}
lemma resize {ps : ∀x,List (BooleanNetwork (k x) (n x))} (hn : Emits ea unaryCode n)
    (hw : Emits ea unaryCode w) (hp : NetsEmits ea ps) :
    NetsEmits ea (fun x=>(ps x).map (fun p=>p.comp (BitArithmetic.resizeWord (n x) (w x)))):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  exact hp.map (g:=fun x p=>p.comp (BitArithmetic.resizeWord (n x) (w x)))
    (hp.get.comp (NetEmits.resize (hn.comp hx.snd) (hw.comp hx.snd)))
lemma all {ps : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k)
    (hp : NetsEmits ea ps) : NetEmits ea (fun x=>BooleanNetwork.all (ps x)):=by
  exact (NetEmits.allOfFn hk hp.length hp.get).congr (fun x=>by rw [List.ofFn_get])
lemma any {ps : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k)
    (hp : NetsEmits ea ps) : NetEmits ea (fun x=>BooleanNetwork.any (ps x)):=by
  exact (NetEmits.anyOfFn hk hp.length hp.get).congr (fun x=>by rw [List.ofFn_get])
end NetsEmits
namespace NetEmits
open BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma tableOrderWidth {f : α→ℕ} (hn : Emits ea unaryCode n) (hf : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>BitArithmetic.tableOrderWidth (n x) (f x)):=
  ((hn.unaryMul (hn.unaryMul hf)).unaryAdd hn).unarySucc
lemma tableOrder {rows : ∀x,List (BooleanNetwork (k x) (n x)×List (BooleanNetwork (k x) (n x)))}
    {a m : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetsEmits ea (fun x=>BitArithmetic.tableNets (rows x))) :
    NetEmits ea (fun x=>BitArithmetic.tableOrder (a x) (m x) (rows x)):=by
  have hw:=tableOrderWidth hn hp.length
  exact (orderFromList hk hw (ha.comp (resize hn hw)) (hm.comp (resize hn hw))
    (NetsEmits.repeated hn (hp.resize hn hw))).comp (resize hw hn)
lemma tableTotient {rows : ∀x,List (BooleanNetwork (k x) (n x)×List (BooleanNetwork (k x) (n x)))}
    {v : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (hv : NetEmits ea v) (hp : NetsEmits ea (fun x=>BitArithmetic.tableNets (rows x))) :
    NetEmits ea (fun x=>BitArithmetic.tableTotient (v x) (rows x)):=
  totientFromList hk hn hv (NetsEmits.repeated hn hp)
lemma componentWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>BitArithmetic.componentWidth (n x)):=
  (hn.unaryMul hn).unarySucc
lemma primeComponent {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.primeComponent (m x) (p x)):=by
  have hw:=componentWidth hn
  exact (((hm.comp (resize hn hw)).pair ((NetsEmits.replicate hn (hp.comp (resize hn hw))).product hk hw)).comp
    (gcd hw)).comp (resize hw hn)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
