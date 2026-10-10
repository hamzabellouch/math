import Mathlib
import OAI.Computability.QuantumFactoring.RetainedListDummy
import OAI.Computability.QuantumFactoring.OrderDecoderPolynomial
import OAI.Computability.QuantumFactoring.RetainedFavorablePolynomial
import OAI.Computability.QuantumFactoring.CompletionFilterPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma ite {α : Type*} {len a b : α→ℕ} (p : α→Prop) [∀x,Decidable (p x)]
    {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>if p x then f x else g x) := by
  apply of_le (PolyAt.add hf hg)
  intro x
  by_cases h : p x
  · rw [ite_eq_left h];omega
  · rw [ite_eq_right h];omega
end NetworkAt
namespace Completion.Expressions
lemma target_poly : RatExprPoly (fun n=>RatExpr.const (Completion.target n) : ℕ→RatExpr (Fin 3)) :=
  RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow PolyBound.id)))
end Completion.Expressions
namespace Completion
lemma rareWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>rareWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma ordinaryWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>ordinaryWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma guessWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>guessWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma retentionWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>retentionWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
end Completion
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
include ht hq
lemma listFilterVars_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).listFilterVars (t xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold listFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.listCoin len
  have hw:=hn.add hc
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((hm.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1)
    (((retainedFavorableCount_at hn ht hq hm).comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma orderFilterVars_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).orderFilterVars (t xi.1) (a xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold orderFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.orderCoin len
  have hw:=hn.add hc
  have ho:=retainedOrder_at hn ht hq ha hm
  have hphi:=retainedTotient_at hn ht hq ho
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((ho.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1) ((hphi.comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma retainedListFilter_at (hpos : ∀x,0<len x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedListFilter (hpos x) (t x) (m x) (raw x)) := by
  unfold retainedListFilter
  have hn:=PolyAt.self len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  have hord : NetworkAt len (fun x=>PhysicalListSlots.ordinaryNet (len x)) :=
    NetworkAt.of_le (PolyAt.ofPoly PreparationPolynomial.transitionWidth len)
      (fun x=>PhysicalListSlots.ordinaryNet_count (len x))
  have hgood := retainedGoodList_at hn ht hq hm ((hr.comp (Completion.ordinaryWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp hord)
  have hcanonical := retainedCanonicalList_at hn ht hq hpos hm (hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      Completion.Expressions.listRateCoin_poly Completion.Expressions.target_poly (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
      hgood hcanonical
lemma listDummyFilter_at
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).listDummyFilter (t x) (m x) (raw x)) := by
  unfold listDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).zeroWord hw)
lemma orderActualFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderActualFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderActualFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have ho:=retainedOrder_at hn ht hq ha hm
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      Completion.Expressions.orderRateCoin_poly Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))
      ((OrderSlots.orderResultNet_poly ha hm (hr.comp (Completion.ordinaryWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))).equalOn ho hn)
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).equalOn (ho.comp (NetworkAt.resizeWord hn hw)) hw)
lemma orderDummyFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderDummyFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).zeroWord hw)
lemma retainedOrderFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedOrderFilter (t x) (a x) (m x) (raw x)) :=
  ((NetworkAt.usableOn (PolyAt.self len) ha hm).band (orderActualFilter_at ht hq ha hm hr)).bor
    ((NetworkAt.usableOn (PolyAt.self len) ha hm).bnot.band (orderDummyFilter_at ht hq ha hm hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
