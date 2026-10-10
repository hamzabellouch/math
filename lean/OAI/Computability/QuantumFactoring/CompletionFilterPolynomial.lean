import Mathlib
import OAI.Computability.QuantumFactoring.RetainedListFilter
import OAI.Computability.QuantumFactoring.RetainedOrderFilter
import OAI.Computability.QuantumFactoring.RetentionExpressionResources
import OAI.Computability.QuantumFactoring.RationalHeightResources
import OAI.Computability.QuantumFactoring.ExpressionAt

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
lemma ofHeight {v : ℕ→Type*} {q : ℕ→ℚ} (h : RatHeightPoly q) :
    RatExprPoly (fun n=>RatExpr.const (q n) : ∀n,RatExpr (v n)) := const h.1 h.2
end RatExprPoly
namespace Completion.Expressions
variable {v : ℕ→Type*} {W t : ℕ→ℕ} {s z : ∀n,RatExpr (v n)}
lemma ordinaryMass_poly (ht : PolyBound t) (hs : RatExprPoly s) :
    RatExprPoly (fun n=>ordinaryMass (t n) (s n)) :=
  (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))).mul hs
lemma coefficient_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>coefficient (W n) (t n) (s n) (z n)) := by
  have hp : RatExprPoly (fun n=>RatExpr.const ((2:ℚ)^(W n+t n+2)) : ∀n,RatExpr (v n)) :=
    RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow ((hW.add ht).add (PolyBound.const 2)))
  exact (RatExprPoly.ofInt (hp.mul (hz.div (ordinaryMass_poly ht hs))).floor).div hp
lemma guess_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>guess (W n) (t n) (s n) (z n)) :=
  ((hz.sub ((coefficient_poly hW ht hs hz).mul (ordinaryMass_poly ht hs))).mul
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow hW))).div
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))
lemma listRateCoin_poly : RatExprPoly (fun n=>listRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).div
    (RatExprPoly.ofNat (OrderTrial.Expressions.coveringPow_poly
      (NatExprPoly.var (fun _=>0)) PolyBound.id))).repeatedSuccess (PolyBound.id.pow 5)
lemma orderRateCoin_poly : RatExprPoly (fun n=>orderRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).mul
    (OrderTrial.Expressions.lambdaE_poly PolyBound.id
      (NatExprPoly.var (fun _=>0)))).repeatedSuccess (PolyBound.id.pow 5)
end Completion.Expressions
lemma retentionNet_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {T : ℕ→ℕ}
    {p : ∀n,RatExpr (v n)} {c : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x)) :
    NetworkAt len (fun x=>retentionNet (T (len x)) (p (len x)) (c (len x)) (vars x)) :=
  (NatExprAt.ofPoly (thresholdExpr_poly hT hp hc) len).isOne hb hv
namespace Completion
lemma predicateFilter_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {W t d : ℕ→ℕ}
    {s z : ∀n,RatExpr (v n)} {coin : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    {branch : ∀x,BooleanNetwork (a x) (t (len x))}
    {good guessGood : ∀x,BooleanNetwork (a x) 1}
    (hW : PolyBound W) (ht : PolyBound t) (hd : PolyBound d)
    (hs : RatExprPoly s) (hz : RatExprPoly z) (hc : NatExprPoly coin)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x))
    (hbranch : NetworkAt len branch) (hgood : NetworkAt len good) (hguess : NetworkAt len guessGood) :
    NetworkAt len (fun x=>predicateFilter (W:=W (len x)) (d (len x))
      (s (len x)) (z (len x)) (vars x) (branch x) (coin (len x)) (good x) (guessGood x)) := by
  have hT : PolyBound (fun n=>coinBits (W n) (t n) (d n)) := by
    unfold coinBits;poly_bound
  have ho:=retentionNet_at hT (Expressions.coefficient_poly hW ht hs hz) hc hb hv
  have hg:=retentionNet_at hT (Expressions.guess_poly hW ht hs hz) hc hb hv
  have hr:=hbranch.zeroWord (PolyAt.ofPoly ht len)
  exact (hr.bnot.band (hgood.band ho)).bor (hr.band (hguess.band hg))
end Completion
end ExactQuantumFactoring

end



end OAI
