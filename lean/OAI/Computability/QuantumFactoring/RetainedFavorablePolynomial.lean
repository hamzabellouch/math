import Mathlib
import OAI.Computability.QuantumFactoring.RetainedFavorable
import OAI.Computability.QuantumFactoring.NetworkAtArithmetic
import OAI.Computability.QuantumFactoring.RetainedNetworkAt

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len k n K : α→ℕ}
lemma usableOn {a m : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>OrderSlots.usableOn (a x) (m x)) :=
  (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma firstOnly {a : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (hK : PolyAt len K) (ha : NetworkAt len a) :
    NetworkAt len (fun x=>TransitionWords.firstOnly (K:=K x) (a x)) := by
  apply of_le ((hn.mul (hK.add (PolyAt.const len 1))).mul
    ((PolyAt.add ha hn).add (PolyAt.const len 1)))
  intro x
  apply TransitionWords.encodeNet_count
  intro i
  by_cases hi:i.val=0
  · rw [ite_eq_left hi];omega
  · rw [ite_eq_right hi,wordConstant_count];omega
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedFavorable_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorable (t x) (a x) (m x)) := by
  let ps:=fun x=>tableNets ((M x).fieldRows (t x))
  let ix:=Σx,{p // p∈ps x}
  let fst:ix→α:=Sigma.fst
  let jx:=Σxi:ix,{q // q∈ps xi.1}
  let both:jx→α:=fun xi=>xi.1.1
  have hps : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=tableNets_at hn hq
  have hl : PolyAt len (fun x=>(ps x).length):=tableNets_length_at hn ht
  apply (NetworkAt.usableOn hn ha hm).band
  apply NetworkAt.bnot
  apply NetworkAt.all_map ps _ hl
  apply NetworkAt.all_map (fun xi:ix=>ps xi.1) _ (hl.pull fst)
  have hp:=hps.pull (fun xi:jx=>xi.1)
  have hq':=hps.pull (fun xi:jx=>⟨xi.1.1,xi.2⟩)
  have hn':=hn.pull both
  have ht':=ht.pull both
  have hquery:=hq.pull both
  have ha':=ha.pull both
  have hm':=hm.pull both
  exact (NetworkAt.dividesOn hn' hp hm').bnot.bor
    ((NetworkAt.dividesOn hn' hq' hm').bnot.bor
      (NetworkAt.sameTwoVal hn'
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hp)
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hq')))
lemma retainedGoodList_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedGoodList (t x) (m x) (y x)) := by
  let param:=fun xi : Σx,Fin ((n x)^5)=>xi.1
  apply NetworkAt.any_ofFn (hn.pow 5)
  exact retainedFavorable_at (hn.pull param) (ht.pull param) (hq.pull param)
    ((hy.pull param).rewire _) (hm.pull param)
lemma retainedCanonicalList_at (hpos : ∀x,0<n x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedCanonicalList (hpos x) (t x) (m x) (y x)) := by
  have ha : NetworkAt len (fun x=>TransitionWords.readNet (y x) ⟨0,pow_pos (hpos x) 5⟩):=
    hy.rewire _
  exact (retainedCanonical_at hn ht hq ha hm).band
    (hy.equalOn (NetworkAt.firstOnly hn (hn.pow 5) ha) (hn.mul ((hn.pow 5).add (PolyAt.const len 1))))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
