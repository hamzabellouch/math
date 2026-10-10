import Mathlib
import OAI.Computability.QuantumFactoring.RationalTemplateEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma powerSumE {M : α→RatExpr v} (hM : REm M) (q : ℕ) : REm (fun x=>powerSum q (M x)):=by
  rcases q with _|_|_|_|_|q <;> simp only [powerSum] <;> rat_emit
lemma fiveTermE {a : α→ℕ→RatExpr v} {lo hi : α→NatExpr v}
    (ha : ∀q,REm (fun x=>a x q)) (hl : NEm lo) (hh : NEm hi) :
    REm (fun x=>fiveTerm (a x) (lo x) (hi x)):=by
  exact rIfNatLe hl hh (rSum (fun q=>rMul (ha q) (rSub (powerSumE (rOfNat hh) q)
    (powerSumE (rOfNat hl) q))) 5) (const _ _ 0)
lemma linearE {a b : α→RatExpr v} {lo hi : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hl : NEm lo) (hh : NEm hi) :
    REm (fun x=>linear (a x) (b x) (lo x) (hi x)):=by
  apply fiveTermE _ hl hh
  intro q;by_cases h0:q=0
  · simpa only [ite_eq_left h0] using ha
  · by_cases h1:q=1
    · simpa only [ite_eq_right h0,ite_eq_left h1] using hb
    · simpa only [ite_eq_right h0,ite_eq_right h1] using (const ea (ratExprCode ev) (0:RatExpr v))
lemma rampE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>ramp (a x) (b x) (M x)):=by
  have hc:=rCeilNat (rDiv (rNeg ha) hb)
  exact rIfLt (const _ _ 0) hb (linearE ha hb hc hM)
    (rIfLt hb (const _ _ 0) (linearE ha hb (const _ _ (NatExpr.const 0)) (nMin hM hc))
      (rMul (rOfNat hM) (rMax (const _ _ 0) ha)))
lemma phaseReE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>phaseRe (a x) (b x) (M x)):=by
  have hl:=linearE (rAdd ha (const _ _ (1/2))) hb (const _ _ (NatExpr.const 0)) hM
  have hr:=rampE ha hb hM
  have hs:=rampE (rSub ha (const _ _ (1/2))) hb hM
  have ht:=rampE (rSub ha (const _ _ 1)) hb hM
  unfold phaseRe;rat_emit
lemma phaseImE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>phaseIm (a x) (b x) (M x)):=by
  have hl:=linearE (rAdd ha (const _ _ (1/2))) hb (const _ _ (NatExpr.const 0)) hM
  have hr:=rampE (rAdd ha (const _ _ (1/4))) hb hM
  have hs:=rampE (rSub ha (const _ _ (1/4))) hb hM
  have ht:=rampE (rSub ha (const _ _ (3/4))) hb hM
  have hu:=rampE (rSub ha (const _ _ (5/4))) hb hM
  unfold phaseIm;rat_emit
lemma binExpr {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    NEm (fun x=>binE (Q x) (d x) (j x)):=by unfold binE;rat_emit
lemma errorE {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>error (Q x) (d x) (j x)):=by
  have h:=binExpr hQ hd hj
  unfold error;rat_emit
lemma offsetE {Q d j t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>offset (Q x) (d x) (j x) (t x)):=by
  have h:=errorE hQ hd hj
  unfold offset;rat_emit
lemma slopeE {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>OrderTrial.Expressions.slope (Q x) (d x) (j x)):=by
  have h:=errorE hQ hd hj
  unfold OrderTrial.Expressions.slope;rat_emit
lemma countE {Q d t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (ht : NEm t) :
    NEm (fun x=>count (Q x) (d x) (t x)):=by unfold count;rat_emit
lemma probabilityE {Q d j t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>probability (Q x) (d x) (j x) (t x)):=by
  have hr:=phaseReE (offsetE hQ hd hj ht) (slopeE hQ hd hj) (countE hQ hd ht)
  have hi:=phaseImE (offsetE hQ hd hj ht) (slopeE hQ hd hj) (countE hQ hd ht)
  unfold probability;rat_emit
end ExactQuantumFactoring.NetworkEmission.Emits

end


end OAI
