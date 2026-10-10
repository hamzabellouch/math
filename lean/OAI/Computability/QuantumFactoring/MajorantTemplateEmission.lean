import Mathlib
import OAI.Computability.QuantumFactoring.DynamicMajorantExpressions
import OAI.Computability.QuantumFactoring.PolynomialTemplateEmission
import OAI.Computability.QuantumFactoring.ProgressionTemplateEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "IEm" => BitStackProgram.Emits ea (intExprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
local notation "PEm" => PolyEmits ea ev
lemma linearPolyE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) :
    PEm (fun x=>linearPoly (d x) (e x)):=by unfold linearPoly;poly_emit
lemma integralZeroE {d : α→NatExpr v} {a : α→PolyExpr v} (hd : NEm d) (ha : PEm a) :
    PEm (fun x=>integralZero (d x) (a x)):=by
  have h:=linearPolyE hd (const _ _ 0)
  exact (PolyEmits.C (rInv (rOfNat hd))).mul (ha.comp h)
lemma integralSlopeE {d : α→NatExpr v} {e : α→RatExpr v} {a b : α→PolyExpr v}
    (hd : NEm d) (he : REm e) (ha : PEm a) (hb : PEm b) :
    PEm (fun x=>integralSlope (d x) (e x) (a x) (b x)):=by
  exact (PolyEmits.C (rInv (rMul (rOfNat hd) he))).mul
    ((hb.comp (linearPolyE hd he)).sub (ha.comp (linearPolyE hd (const _ _ 0))))
lemma massZeroE {d : α→NatExpr v} (hd : NEm d) (q : ℤ) :
    PEm (fun x=>massZero (d x) q):=by
  exact ((integralZeroE hd (PolyEmits.literal (phaseRePoly q))).pow 2).add
    ((integralZeroE hd (PolyEmits.literal (phaseImPoly q))).pow 2)
lemma massSlopeE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q r : ℤ) :
    PEm (fun x=>massSlope (d x) (e x) q r):=by
  exact ((integralSlopeE hd he (PolyEmits.literal (splineRePoly q)) (PolyEmits.literal (splineRePoly r))).pow 2).add
    ((integralSlopeE hd he (PolyEmits.literal (splineImPoly q)) (PolyEmits.literal (splineImPoly r))).pow 2)
lemma massCoeffE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q r : ℤ) (k : ℕ) :
    REm (fun x=>massCoeff (d x) (e x) q r k):=
  rIfEq he (const _ _ 0) ((massZeroE hd q).coeff k) ((massSlopeE hd he q r).coeff k)
lemma roundedE {D : α→NatExpr v} {a : α→RatExpr v} (hD : NEm D) (ha : REm a) :
    REm (fun x=>rounded (D x) (a x)):=by unfold rounded;rat_emit
lemma roundingDenE {Q B : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) :
    NEm (fun x=>roundingDen (Q x) (B x)):=nmul hQ (nPow hB 8)
lemma lowE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q : ℤ×ℤ) :
    NEm (fun x=>low (d x) (e x) q):=by unfold low;rat_emit
lemma highE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q : ℤ×ℤ) :
    NEm (fun x=>high (d x) (e x) q):=by unfold high;rat_emit
lemma pieceSumE {Q B d j : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (q : ℤ×ℤ) :
    REm (fun x=>pieceSum (Q x) (B x) (d x) (j x) q):=by
  have he:=errorE hQ hd hj
  have hl:=lowE hd he q;have hh:=highE hd he q
  exact rAdd (fiveTermE (fun k=>roundedE (roundingDenE hQ hB) (massCoeffE hd he q.1 q.2 k)) hl hh)
    (rMul (rOfNat (nsub hh hl)) (rDiv (const _ _ 64) (rOfNat hQ)))
lemma majorantSumExpr {Q B d j : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>majorantSumE (Q x) (B x) (d x) (j x)):=
  rDiv (rSumList (fun q=>pieceSumE hQ hB hd hj q) quarterList) (const _ _ 2)
lemma dynamicRampE {q : α→IntExpr v} (hq : IEm q) (a : ℤ) :
    PEm (fun x=>dynamicRamp (q x) a):=by unfold dynamicRamp;poly_emit
lemma dynamicRampLinE {q : α→IntExpr v} (hq : IEm q) (a : ℤ) :
    PEm (fun x=>dynamicRampLin (q x) a):=by unfold dynamicRampLin;poly_emit
lemma dynamicSplineReE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicSplineRe (q x)):=by
  have h0:=dynamicRampE hq 0;have h2:=dynamicRampE hq 2;have h4:=dynamicRampE hq 4
  unfold dynamicSplineRe;poly_emit
lemma dynamicSplineImE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicSplineIm (q x)):=by
  have h0:=dynamicRampE hq (-1);have h2:=dynamicRampE hq 1;have h4:=dynamicRampE hq 3;have h5:=dynamicRampE hq 5
  unfold dynamicSplineIm;poly_emit
lemma dynamicPhaseReE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicPhaseRe (q x)):=by
  have h0:=dynamicRampLinE hq 0;have h2:=dynamicRampLinE hq 2;have h4:=dynamicRampLinE hq 4
  unfold dynamicPhaseRe;poly_emit
lemma dynamicPhaseImE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicPhaseIm (q x)):=by
  have h0:=dynamicRampLinE hq (-1);have h2:=dynamicRampLinE hq 1;have h4:=dynamicRampLinE hq 3;have h5:=dynamicRampLinE hq 5
  unfold dynamicPhaseIm;poly_emit
lemma dynamicMassZeroE {d : α→NatExpr v} {q : α→IntExpr v} (hd : NEm d) (hq : IEm q) :
    PEm (fun x=>dynamicMassZero (d x) (q x)):=
  ((integralZeroE hd (dynamicPhaseReE hq)).pow 2).add ((integralZeroE hd (dynamicPhaseImE hq)).pow 2)
lemma dynamicMassSlopeE {d : α→NatExpr v} {e : α→RatExpr v} {q r : α→IntExpr v}
    (hd : NEm d) (he : REm e) (hq : IEm q) (hr : IEm r) :
    PEm (fun x=>dynamicMassSlope (d x) (e x) (q x) (r x)):=
  ((integralSlopeE hd he (dynamicSplineReE hq) (dynamicSplineReE hr)).pow 2).add
    ((integralSlopeE hd he (dynamicSplineImE hq) (dynamicSplineImE hr)).pow 2)
lemma dynamicMassCoeffE {d : α→NatExpr v} {e : α→RatExpr v} {q r : α→IntExpr v}
    (hd : NEm d) (he : REm e) (hq : IEm q) (hr : IEm r) (k : ℕ) :
    REm (fun x=>dynamicMassCoeff (d x) (e x) (q x) (r x) k):=
  rIfEq he (const _ _ 0) ((dynamicMassZeroE hd hq).coeff k) ((dynamicMassSlopeE hd he hq hr).coeff k)
lemma quarterE {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>quarter (a x)):=by unfold quarter;rat_emit
lemma majorantExpr {Q B d j u : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (hu : NEm u) :
    REm (fun x=>majorantE (Q x) (B x) (d x) (j x) (u x)):=by
  have he:=errorE hQ hd hj
  have ha:=rDiv (rOfNat hu) (rOfNat hd)
  exact rAdd (rSum (fun k=>rMul (roundedE (roundingDenE hQ hB)
    (dynamicMassCoeffE hd he (quarterE ha) (quarterE (rAdd ha he)) k)) (rPow (rOfNat hu) k)) 5)
      (rDiv (const _ _ 64) (rOfNat hQ))
end ExactQuantumFactoring.NetworkEmission.Emits

end



end OAI
