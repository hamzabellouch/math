import Mathlib
import OAI.Computability.QuantumFactoring.TrialControlCircuit
import OAI.Computability.QuantumFactoring.RetentionExpressionResources
import OAI.Computability.QuantumFactoring.ExpressionAt
import OAI.Computability.QuantumFactoring.NetworkAtArithmetic
import OAI.Computability.QuantumFactoring.PreparationPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
variable {α : Type*} {len k w : α→ℕ}
lemma decodeVars_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t) (hc : NetworkAt len c) :
    ∃p : Polynomial ℕ,∀x (i : DecodeVar),
      ((match i with | .den=>d x | .num=>j x | .residue=>t x | .coin=>c x) :
        BooleanNetwork (k x) (w x)).net.count≤p.eval (len x) := by
  obtain ⟨p,hp⟩:=((hd.add hj).add ht).add hc
  refine ⟨p,fun x i=>?_⟩
  have h:=hp x
  dsimp only at h
  cases i <;> dsimp only <;> omega

lemma firstRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>firstRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.firstE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.firstE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma secondRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>secondRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.secondE n (.var DecodeVar.den) (.var .num) (.var .residue)) :=
    Expressions.secondE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma thirdRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>thirdRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.lastE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.lastE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma labelValidNet_poly {a m d j : ∀x,BooleanNetwork (k x) (w x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hj : NetworkAt len j) (hw : PolyAt len w) :
    NetworkAt len (fun x=>labelValidNet (len x) (a x) (m x) (d x) (j x)) := by
  let c:=fun x=>(a x).net.count+(m x).net.count+(d x).net.count+(j x).net.count
  have hc : PolyAt len c:=((ha.add hm).add hd).add hj
  have hg : PolyAt len (fun x=>2*w x*(216*w x*w x+300*w x+100)) := by
    exact ((PolyAt.const len 2).mul hw).mul ((((PolyAt.const len 216).mul hw).mul hw).add
      ((PolyAt.const len 300).mul hw) |>.add (PolyAt.const len 100))
  have hp : PolyAt len (fun x=>w x+w x*(3672*w x*w x+436*w x+36)) := by
    exact hw.add (hw.mul ((((PolyAt.const len 3672).mul hw).mul hw).add
      ((PolyAt.const len 436).mul hw) |>.add (PolyAt.const len 36)))
  apply NetworkAt.of_le (bound:=fun x=>9*c x+
    (2*w x*(216*w x*w x+300*w x+100))+(w x+w x*(3672*w x*w x+436*w x+36))+344*w x+70)
  · poly_at
  · intro x
    have h:=labelValidNet_count (len x) (a x) (m x) (d x) (j x)
      (c:=c x) (by dsimp [c];omega) (by dsimp [c];omega)
      (by dsimp [c];omega) (by dsimp [c];omega)
    omega
lemma trialAcceptOn_poly {a m mode d j t c : ∀x,BooleanNetwork (k x) (w x)}
    {selected : ∀x,BooleanNetwork (k x) 1}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hmode : NetworkAt len mode)
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hs : NetworkAt len selected) (hw : PolyAt len w) :
    NetworkAt len (fun x=>trialAcceptOn (len x) (a x) (m x) (mode x) (d x) (j x) (t x) (c x) (selected x)) := by
  have h2:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 2) hw
  have h3:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 3) hw
  have h1:=firstRetNet_poly hd hj ht hc hw
  have hsecond:=secondRetNet_poly hd hj ht hc hw
  have hthird:=thirdRetNet_poly hd hj ht hc hw
  exact (labelValidNet_poly ha hm hd hj hw).band
    (((hmode.wordLt h2 hw).band (hs.band h1)).bor
      (((hmode.equalOn h2 hw).band ((ht.wordLt hd hw).band hsecond)).bor
        ((hmode.equalOn h3 hw).band hthird)))
end OrderTrial
end ExactQuantumFactoring

end


end OAI
