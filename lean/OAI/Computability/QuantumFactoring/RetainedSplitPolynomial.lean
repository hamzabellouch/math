import Mathlib
import OAI.Computability.QuantumFactoring.RetainedSplitFilter
import OAI.Computability.QuantumFactoring.PrimalityPolynomial
import OAI.Computability.QuantumFactoring.RetainedFilterPolynomial
import OAI.Computability.QuantumFactoring.ActualDivisorPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma primeWord {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.primeWord (n x)) :=
  of_le (PolyAt.comp PreparationPolynomial.primeBound_poly hn) (fun x=>primeWord_count (n x))
lemma perfectPowerNet {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.perfectPowerNet (n x)) :=
  of_le (((hn.add (PolyAt.const len 1)).mul
    ((PolyAt.comp PreparationPolynomial.perfectCheckBound_poly hn).add (PolyAt.const len 4))).add
    (PolyAt.const len 1)) (fun x=>perfectPowerNet_count (n x))
lemma hardOn {α : Type*} {len a n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x)}
    (hn : PolyAt len n) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>UniversalSplit.hardOn (m x)) := by
  have hr:=PolyAt.comp PreparationPolynomial.rootWidth_poly hn
  exact (((NetworkAt.wordConstant _ hn).wordLe hm hn).band (hm.comp (primeWord hn)).bnot).band
    ((hm.evenOn hn).bnot.band ((hm.comp (NetworkAt.resizeWord hn hr)).comp (perfectPowerNet hn)).bnot)
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
variable {raw : ∀x,BooleanNetwork ((M x).width (t x)) (FixedSplit.width (len x))}
variable (hr : NetworkAt len raw)
include hr
omit ht hq in
lemma splitModulus_at : NetworkAt len (fun x=>(M x).splitModulus (t x) (raw x)) :=
  hr.comp (FixedSplit.modulusNet_poly.pull len)
omit ht hq in
lemma splitList_at : NetworkAt len (fun x=>(M x).splitList (t x) (raw x)) :=
  (hr.comp (NetworkAt.select _)).comp (NetworkAt.select _)
omit ht hq in
lemma splitBase_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitBase (t xi.1) (raw xi.1) xi.2) := by
  unfold splitBase
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualBaseNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
omit ht hq in
lemma splitOrder_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitOrder (t xi.1) (raw xi.1) xi.2) := by
  unfold splitOrder
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualOrderRawNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
include ht hq in
lemma splitActualFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).splitActualFilter (hpos x) (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (retainedListFilter_at ht hq hpos (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (retainedOrderFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma splitDummyFilter_at :
    NetworkAt len (fun x=>(M x).splitDummyFilter (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (listDummyFilter_at ht hq (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (orderDummyFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma retainedSplitFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).retainedSplitFilter (hpos x) (t x) (raw x)) := by
  have hh:=NetworkAt.hardOn (PolyAt.self len) (splitModulus_at hr)
  exact (hh.band (splitActualFilter_at ht hq hr hpos)).bor
    (hh.bnot.band (splitDummyFilter_at ht hq hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
