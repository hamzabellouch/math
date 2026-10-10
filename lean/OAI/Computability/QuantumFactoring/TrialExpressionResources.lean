import Mathlib
import OAI.Computability.QuantumFactoring.PolySchemaPoly

namespace OAI



section

namespace ExactQuantumFactoring
namespace NatExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, NatExpr (v n)}
lemma min (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).min (b n)) := ha.iteLe hb ha hb
lemma max (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).max (b n)) := ha.iteLe hb hb ha
end NatExprPoly
namespace RatExprPoly
lemma sumList {v : ℕ → Type*} {α : Type*} {f : α → ∀ n, RatExpr (v n)}
    (hf : ∀ i, RatExprPoly (f i)) (xs : List α) :
    RatExprPoly (fun n => RatExpr.sumList (fun i => f i n) xs) := by
  induction xs with
  | nil => exact constant 0
  | cons i xs ih => exact (hf i).add ih
end RatExprPoly

namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {a b η : ∀ n, RatExpr (v n)}
  {Q B d j t u lo hi : ∀ n, NatExpr (v n)}
lemma powerSum_poly (ha : RatExprPoly a) (q : ℕ) :
    RatExprPoly (fun n => powerSum q (a n)) := by
  rcases q with _|_|_|_|_|q <;> simp only [powerSum] <;> expr_poly
lemma fiveTerm_poly {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i))
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => fiveTerm (fun i => f i n) (lo n) (hi n)) := by
  exact RatExprPoly.ifNatLe hl hh (RatExprPoly.sum (fun i => (hf i).mul
    ((powerSum_poly (RatExprPoly.ofNat hh) i).sub (powerSum_poly (RatExprPoly.ofNat hl) i))) 5) (RatExprPoly.constant 0)
lemma linear_poly (ha : RatExprPoly a) (hb : RatExprPoly b)
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => linear (a n) (b n) (lo n) (hi n)) := by
  apply fiveTerm_poly _ hl hh
  intro q
  exact RatExprPoly.ite (fun _=>q=0) ha
    (RatExprPoly.ite (fun _=>q=1) hb (RatExprPoly.constant 0))
lemma ramp_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => ramp (a n) (b n) (d n)) := by
  have hx := (ha.negation.div hb).ceilNat
  have h1 := linear_poly ha hb hx hd
  have h2 := linear_poly ha hb (NatExprPoly.constPoly (PolyBound.const 0)) (hd.min hx)
  unfold ramp
  expr_poly
lemma phaseRe_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseRe (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly ha hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb hd
  have h4 := ramp_poly (ha.sub (RatExprPoly.constant 1)) hb hd
  unfold phaseRe
  expr_poly
lemma phaseIm_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseIm (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h4 := ramp_poly (ha.sub ((RatExprPoly.constant 3).div (RatExprPoly.constant 4))) hb hd
  have h5 := ramp_poly (ha.sub ((RatExprPoly.constant 5).div (RatExprPoly.constant 4))) hb hd
  unfold phaseIm
  expr_poly
lemma binE_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    NatExprPoly (fun n => binE (Q n) (d n) (j n)) := by
  unfold binE
  expr_poly
lemma error_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => error (Q n) (d n) (j n)) := by
  have h := binE_poly hQ hd hj
  unfold error
  expr_poly
lemma offset_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => offset (Q n) (d n) (j n) (t n)) := by
  have h := error_poly hQ hd hj
  unfold offset
  expr_poly
lemma slope_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => slope (Q n) (d n) (j n)) := by
  have h := error_poly hQ hd hj
  unfold slope
  expr_poly
lemma count_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (ht : NatExprPoly t) :
    NatExprPoly (fun n => count (Q n) (d n) (t n)) := by
  unfold count
  expr_poly
lemma probability_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => probability (Q n) (d n) (j n) (t n)) := by
  have ho := offset_poly hQ hd hj ht
  have hs := slope_poly hQ hd hj
  have hc := count_poly hQ hd ht
  have hr := phaseRe_poly ho hs hc
  have hi := phaseIm_poly ho hs hc
  unfold probability
  expr_poly
lemma rounded_poly (hd : NatExprPoly d) (ha : RatExprPoly a) :
    RatExprPoly (fun n => rounded (d n) (a n)) := by unfold rounded; expr_poly
lemma roundingDen_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) :
    NatExprPoly (fun n => roundingDen (Q n) (B n)) := hQ.mul (hB.pow (PolyBound.const 8))
lemma quarter_poly (ha : RatExprPoly a) : IntExprPoly (fun n => quarter (a n)) := by
  unfold quarter; expr_poly
lemma majorantE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (hu : NatExprPoly u) :
    RatExprPoly (fun n => majorantE (Q n) (B n) (d n) (j n) (u n)) := by
  have he := error_poly hQ hd hj
  have h0 := quarter_poly ((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd))
  have h1 := quarter_poly (((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd)).add he)
  have hs := RatExprPoly.sum (fun k =>
    (rounded_poly (roundingDen_poly hQ hB) (dynamicMassCoeff_poly hd he h0 h1 k)).mul
      ((RatExprPoly.ofNat hu).pow k)) 5
  unfold majorantE
  exact hs.add ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ))
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI
