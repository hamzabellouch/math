import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformGrid

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

variable {t : ℕ} {h : Fin t → Bool}

def secondAddress (h : Fin t → Bool) (pos : Fin t → Fin 3) : AExpr :=
  .add ((AExpr.mul ((AExpr.reg 1).pow 3) (.const 2)).pow t) (secondExpr h pos)
def leftExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  .add (signatureLookup (fun s=>tableNumber (T.leftTable pos s)))
    (.mul (.const (2^((2^3)^t))) (if T.first then firstExpr t else secondAddress h pos))
def rightExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  .add (.const (tableNumber T.rightTable)) (.mul (.const (2^((2^3)^t))) (secondAddress h pos))
def signExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  signatureLookup (fun s=>(T.localSign pos s).toNat)

lemma secondAddress_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondAddress h pos).eval (inputTuple input u)=
      (input.«variables»^3*2)^t+secondNumber (fun j=>equations input (u j)) h pos := by
  simp only [secondAddress,AExpr.eval,AExpr.eval_pow,inputTuple_reg1,secondExpr_eval]
lemma leftExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (leftExpr T pos).eval (inputTuple input u)=T.leftNumber (fun j=>equations input (u j)) pos := by
  simp only [leftExpr,AExpr.eval,signatureLookup_eval,Query.leftNumber]
  cases T.first <;> simp only [Bool.false_eq_true,ite_false,ite_true,firstExpr_eval,secondAddress_eval]
lemma rightExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (rightExpr T pos).eval (inputTuple input u)=T.rightNumber (fun j=>equations input (u j)) pos := by
  simp only [rightExpr,AExpr.eval,secondAddress_eval,Query.rightNumber]
lemma signExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (signExpr T pos).eval (inputTuple input u)=
      ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).equal.toNat := by
  rw [Query.signed_equal]
  exact signatureLookup_eval input u _

def queryWords (T : Query h) (pos : Fin t → Fin 3) (v : List ℕ) : List ℕ :=
  [(leftExpr T pos).eval v,(rightExpr T pos).eval v,(signExpr T pos).eval v]
def queryProgram (T : Query h) (pos : Fin t → Fin 3) : PolyProgram (queryWords T pos) :=
  ((leftExpr T pos).program.cons ((rightExpr T pos).program.cons
    ((signExpr T pos).program.cons PolyProgram.nil))).ofEq (by intro v; rfl)

lemma queryWords_eq (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    queryWords T pos (inputTuple input u)=
      [(variableCode ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).left).val,
       (variableCode ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).right).val,
       ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).equal.toNat] := by
  simp only [queryWords,leftExpr_eval,rightExpr_eval,signExpr_eval,Query.left_number,Query.right_number]

end MinUncut.Costed.SourceWords

namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
lemma O.demandDigit {i : ∀p,A p → ℕ} (hi : c.Out i) :
    O c (fun p x=>MinUncut.Costed.SourceWords.tupleDigit (i p x)) :=
  ((O.fixed (.reg 0)).div ((O.fixed (.reg 2)).pow hi)).mod (O.fixed (.reg 2))
lemma O.slotExpr {i j : ∀p,A p → ℕ} (hi : c.Out i) (hj : c.Out j) :
    O c (fun p x=>MinUncut.Costed.SourceWords.slotExpr (i p x) (j p x)) :=
  ((O.fixed (.const 3)).add ((O.fixed (.const 4)).mul (O.demandDigit hi))).add (O.const hj) |>.at
lemma O.equationExpr {i : ∀p,A p → ℕ} (hi : c.Out i) :
    O c (fun p x=>MinUncut.Costed.SourceWords.equationExpr (i p x)) := by
  have hp : (c.prod (fin (fun _ : P=>3) (Computable.const 3))).Out (fun _ x=>x.2.val) :=
    (out_code (fin (P:=P) (fun _=>3) (Computable.const 3))).second
  have hw := (O.slotExpr hi.first hp).mul ((O.fixed (.reg 1)).pow hp)
  exact (O.slotExpr hi (out_const c (Computable.const 3))).add
    ((O.fixed (.const 2)).mul (hw.sum_fin (Computable.const 3)))
lemma c_firstExpr : C MinUncut.Costed.SourceWords.firstExpr := by
  let c := unitN.prod (fin id Computable.id)
  have hi : c.Out (fun _ x=>x.2.val) := (out_code (fin id Computable.id)).second
  have hbase : O c (fun _ _=>.mul ((AExpr.reg 1).pow 3) (.const 2)) := O.fixed _
  exact ((O.equationExpr hi).mul (hbase.pow hi) |>.sum_fin Computable.id).toC
lemma O.secondExpr {t : P → ℕ} (ht : Computable t) {h : ∀p,A p → Fin (t p) → Bool}
    {pos : ∀p,A p → Fin (t p) → Fin 3}
    (hh : c.Map ((fin t ht).function bool) h)
    (hp : c.Map (Alphabet.positionsList t ht) pos) :
    O c (fun p x=>MinUncut.Costed.SourceWords.secondExpr (h p x) (pos p x)) := by
  let d:=c.prod (fin t ht)
  have hi : d.Out (fun _ x=>x.2.val) := (out_code (fin t ht)).second
  have hj := map_apply hp.first (map_snd c (fin t ht))
  have hjn := (out_code (fin (fun _ : P=>3) (Computable.const 3))).comp hj
  have hb:=map_apply hh.first (map_snd c (fin t ht))
  have left:=O.slotExpr hi hjn
  have right:=(O.fixed (.reg 1)).add (O.equationExpr hi)
  have base : O d (fun _ _=>.add (.reg 1) (.mul ((AExpr.reg 1).pow 3) (.const 2))) := O.fixed _
  exact ((O.choose hb left right).mul (base.pow hi)).sum_fin ht

lemma c_demandSignatureExpr : C MinUncut.Costed.SourceWords.signatureExpr := by
  let axes:=fin (P:=ℕ) id Computable.id
  let pos:=fin (P:=ℕ) (fun _=>3) (Computable.const 3)
  let c:=unitN.prod axes
  let d:=c.prod pos
  let e:=d.prod pos
  have hi : e.Out (fun _ x=>x.1.1.2.val) := (out_code axes).second.first.first
  have hp : e.Out (fun _ x=>x.1.2.val) := (out_code pos).second.first
  have hq : e.Out (fun _ x=>x.2.val) := (out_code pos).second
  have eqs := (O.slotExpr hi hp).eq (O.slotExpr hi hq)
  have powq := hq.map (ca_pow (Computable.const 2) Computable.id)
  have inner := (eqs.mul (O.const powq)).sum_fin (Computable.const 3)
  have pcode : d.Out (fun _ x=>x.2.val) := (out_code pos).second
  have powp := pcode.map (ca_pow (Computable.const (2^3)) Computable.id)
  have mid := (inner.mul (O.const powp)).sum_fin (Computable.const 3)
  have ii : c.Out (fun _ x=>x.2.val) := (out_code axes).second
  have outer := (mid.mul (O.const (ii.map (ca_pow (Computable.const ((2^3)^3)) Computable.id)))).sum_fin Computable.id
  have rhs := ((O.slotExpr ii (out_const c (Computable.const 3))).mul
    (O.const (ii.map (ca_pow (Computable.const 2) Computable.id)))).sum_fin Computable.id
  have co := O.const (out_const unitN (ca_pow (Computable.const ((2^3)^3)) Computable.id))
  exact (outer.add (co.mul rhs)).toC
lemma O.demandLookup {t : P → ℕ} (ht : Computable t)
    {f : ∀p,A p × Signature (Fin (t p)) → ℕ}
    (hf : (c.prod (Alphabet.signatures t ht)).Out f) :
    O c (fun p x=>MinUncut.Costed.SourceWords.signatureLookup (fun s=>f p (x,s))) :=
  (O.fromC (c_demandSignatureExpr.precomp ht)).lookup (out_constantTable hf)
end MinUncut.Preprocess.Syntax

end

end OAI
