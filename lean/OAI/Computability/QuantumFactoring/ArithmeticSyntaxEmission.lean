import Mathlib
import OAI.Computability.QuantumFactoring.RationalConditionals
import OAI.Computability.QuantumFactoring.RationalRounding
import OAI.Computability.QuantumFactoring.BitStackRationals
import OAI.Computability.QuantumFactoring.SignedSyntaxEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "IEm" => BitStackProgram.Emits ea (intExprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma iOfNat {a : α→NatExpr v} (ha : NEm a) : IEm (fun x=>IntExpr.ofNat (a x)):=
  imk ha (const _ _ (NatExpr.const 0))
lemma iOfInt {a : α→ℤ} (ha : BitStackProgram.Emits ea intCode a) : IEm (fun x=>IntExpr.ofInt (a x)):=by
  exact imk (nconst ((ofProcedure Emission.intToNatP).comp ha))
    (nconst ((ofProcedure Emission.intToNatP).comp ((ofProcedure Procedure.intNeg).comp ha)))
lemma iAdd {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).add (b x)):=
  imk (nadd (ipos ha) (ipos hb)) (nadd (ineg ha) (ineg hb))
lemma iNeg {a : α→IntExpr v} (ha : IEm a) : IEm (fun x=>(a x).negation):=imk (ineg ha) (ipos ha)
lemma iSub {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).sub (b x)):=iAdd ha (iNeg hb)
lemma iMul {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).mul (b x)):=by
  unfold IntExpr.mul;expr_emit
lemma iScale {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    IEm (fun x=>(a x).scale (b x)):=iMul ha (iOfNat hb)
lemma iToNat {a : α→IntExpr v} (ha : IEm a) : NEm (fun x=>(a x).toNat):=nsub (ipos ha) (ineg ha)
lemma iNatAbs {a : α→IntExpr v} (ha : IEm a) : NEm (fun x=>(a x).natAbs):=
  nadd (nsub (ipos ha) (ineg ha)) (nsub (ineg ha) (ipos ha))
lemma iIte {a b : α→NatExpr v} {c d : α→IntExpr v} (ha : NEm a) (hb : NEm b) (hc : IEm c) (hd : IEm d) :
    IEm (fun x=>IntExpr.iteLe (a x) (b x) (c x) (d x)):=by unfold IntExpr.iteLe;expr_emit
lemma iIfLe {a b c d : α→IntExpr v} (ha : IEm a) (hb : IEm b) (hc : IEm c) (hd : IEm d) :
    IEm (fun x=>IntExpr.ifLe (a x) (b x) (c x) (d x)):=
  iIte (nadd (ipos ha) (ineg hb)) (nadd (ipos hb) (ineg ha)) hc hd
lemma rOfInt {a : α→IntExpr v} (ha : IEm a) : REm (fun x=>RatExpr.ofInt (a x)):=rmk ha (const _ _ (NatExpr.const 1))
lemma rOfNat {a : α→NatExpr v} (ha : NEm a) : REm (fun x=>RatExpr.ofNat (a x)):=rOfInt (iOfNat ha)
lemma rConst {a : α→ℚ} (ha : BitStackProgram.Emits ea ratCode a) : REm (fun x=>RatExpr.const (a x)):=
  rmk (iOfInt ((ofProcedure Procedure.ratNum).comp ha)) (nconst ((ofProcedure Procedure.ratDen).comp ha))
lemma rNormalize {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).normalize):=
  rmk (iIte (rden ha) (const _ _ (NatExpr.const 0)) (const _ _ (IntExpr.ofInt 0)) (rnum ha))
    (nite (rden ha) (const _ _ (NatExpr.const 0)) (const _ _ (NatExpr.const 1)) (rden ha))
lemma rAdd {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).add (b x)):=by
  have hc:=rNormalize ha;have hd:=rNormalize hb
  exact rmk (iAdd (iScale (rnum hc) (rden hd)) (iScale (rnum hd) (rden hc))) (nmul (rden hc) (rden hd))
lemma rNeg {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).negation):=rmk (iNeg (rnum ha)) (rden ha)
lemma rSub {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).sub (b x)):=rAdd ha (rNeg hb)
lemma rMul {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).mul (b x)):=
  rmk (iMul (rnum ha) (rnum hb)) (nmul (rden ha) (rden hb))
lemma rInv {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).inverse):=
  rmk (iScale (rnum ha) (rden ha)) (nmul (iNatAbs (rnum ha)) (iNatAbs (rnum ha)))
lemma rDiv {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).div (b x)):=rMul ha (rInv hb)
lemma rPow {a : α→RatExpr v} (ha : REm a) (k : ℕ) : REm (fun x=>(a x).pow k):=by
  induction k with
  | zero=>exact const _ _ (RatExpr.const 1)
  | succ k ih=>exact rMul ih ha
lemma rIfNatLe {a b : α→NatExpr v} {c d : α→RatExpr v} (ha : NEm a) (hb : NEm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifNatLe (a x) (b x) (c x) (d x)):=
  rmk (iIte ha hb (rnum hc) (rnum hd)) (nite ha hb (rden hc) (rden hd))
lemma rIfIntLe {a b : α→IntExpr v} {c d : α→RatExpr v} (ha : IEm a) (hb : IEm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifIntLe (a x) (b x) (c x) (d x)):=
  rIfNatLe (nadd (ipos ha) (ineg hb)) (nadd (ipos hb) (ineg ha)) hc hd
lemma rIfLe {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifLe (a x) (b x) (c x) (d x)):=by
  have he:=rNormalize ha;have hf:=rNormalize hb
  exact rIfIntLe (iScale (rnum he) (rden hf)) (iScale (rnum hf) (rden he)) hc hd
lemma rIfLt {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifLt (a x) (b x) (c x) (d x)):=rIfLe hb ha hd hc
lemma rIfEq {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifEq (a x) (b x) (c x) (d x)):=rIfLe ha hb (rIfLe hb ha hc hd) hd
lemma rMax {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>RatExpr.max (a x) (b x)):=rIfLe ha hb hb ha
lemma rMin {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>RatExpr.min (a x) (b x)):=rIfLe ha hb ha hb
lemma iCeilRatio {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    NEm (fun x=>(a x).ceilRatioNat (b x)):=ndiv (nsub (nadd (iToNat ha) hb) (const _ _ (NatExpr.const 1))) hb
lemma iFloorRatio {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    IEm (fun x=>(a x).floorRatio (b x)):=iSub (iOfNat (ndiv (iToNat ha) hb)) (iOfNat (iCeilRatio (iNeg ha) hb))
lemma rCeilNat {a : α→RatExpr v} (ha : REm a) : NEm (fun x=>(a x).ceilNat):=iCeilRatio (rnum ha) (rden ha)
lemma rFloor {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>(a x).floor):=iFloorRatio (rnum ha) (rden ha)
lemma rCeil {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>(a x).ceil):=iNeg (rFloor (rNeg ha))
end ExactQuantumFactoring.NetworkEmission.Emits

end


end OAI
