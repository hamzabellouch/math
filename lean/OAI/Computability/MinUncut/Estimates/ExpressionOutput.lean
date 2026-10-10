import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformRestrict
import OAI.Computability.MinUncut.Encoding.DerivedResolver
import OAI.Computability.MinUncut.Estimates.ExpressionEffectivity

namespace OAI

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type}
def O (c : UEncoding P A) (f : ∀p,A p → AExpr) : Prop := c.Out (fun p x=>(f p x).program.code)
variable {c : UEncoding P A}
lemma O.fixed (e : AExpr) : O c (fun _ _=>e) := out_const c (Computable.const _)
lemma O.const {f : ∀p,A p → ℕ} (hf : c.Out f) : O c (fun p x=>.const (f p x)) := hf.map p_constCode.to_comp
lemma O.reg {f : ∀p,A p → ℕ} (hf : c.Out f) : O c (fun p x=>.reg (f p x)) := hf.map p_atCode.to_comp
lemma O.add {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.add (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.add.code).to_comp
lemma O.sub {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.sub (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.sub.code).to_comp
lemma O.mul {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.mul (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.mul.code).to_comp
lemma O.div {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.div (a p x) (b p x)) :=
  ha.map₂ hb (p_bin Division.quotient.code).to_comp
lemma O.mod {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.mod (a p x) (b p x)) :=
  ha.map₂ hb (p_bin Division.remainder.code).to_comp
lemma O.cond {e a b : ∀p,A p → AExpr} (he : O c e) (ha : O c a) (hb : O c b) :
    O c (fun p x=>.cond (e p x) (a p x) (b p x)) := by
  have hh := (he.pair (ha.pair hb)).map p_branch.to_comp
  exact hh.ofEq (fun p x=>(cond_code (e p x) (a p x) (b p x)).symm)
lemma O.eq {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.eq (a p x) (b p x)) := by
  have hh := ((ha.sub hb).add (hb.sub ha)).cond (O.fixed (.const 1)) (O.fixed (.const 0))
  exact hh.ofEq (fun p x=>(eq_code (a p x) (b p x)).symm)
lemma O.le {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.le (a p x) (b p x)) := by
  have hh := (ha.sub hb).cond (O.fixed (.const 1)) (O.fixed (.const 0))
  exact hh.ofEq (fun p x=>(le_code (a p x) (b p x)).symm)
lemma O.at {a : ∀p,A p → AExpr} (ha : O c a) : O c (fun p x=>.at (a p x)) := by
  have hh := ha.map (computable_comp.comp (Computable.const PolyProgram.dynamic.code)
    (computable_cons.comp Computable.id (Computable.const Code.id)))
  exact hh.ofEq (fun p x=>(at_code (a p x)).symm)
lemma O.choose {q : ∀p,A p → Bool} {a b : ∀p,A p → AExpr}
    (hq : c.Map bool q) (ha : O c a) (hb : O c b) : O c (fun p x=>if q p x then a p x else b p x) := by
  apply (Out.cond hq ha hb).ofEq
  intro p x
  change (if q p x = true then (a p x).program.code else (b p x).program.code) =
    (if q p x = true then a p x else b p x).program.code
  by_cases h : q p x = true
  · rw [ite_eq_left h]
    exact (congrArg (fun e : AExpr=>e.program.code) (ite_eq_left h : (if q p x = true then a p x else b p x)=a p x)).symm
  · rw [ite_eq_right h]
    exact (congrArg (fun e : AExpr=>e.program.code) (ite_eq_right h : (if q p x = true then a p x else b p x)=b p x)).symm

def powCode (a : Code) (n : ℕ) : Code := Nat.rec (AExpr.const 1).program.code (fun _ ih=>bin PolyProgram.mul.code ih a) n
lemma c_powCode : Computable₂ powCode := by
  exact Computable.nat_rec Computable.snd (Computable.const _)
    ((p_bin PolyProgram.mul.code).to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)).to₂
lemma O.pow {a : ∀p,A p → AExpr} {n : ∀p,A p → ℕ} (ha : O c a) (hn : c.Out n) :
    O c (fun p x=>(a p x).pow (n p x)) :=
  (ha.map₂ hn c_powCode).ofEq (fun p x=>powCode_eq (a p x) (n p x))
lemma O.sum {as : ∀p,A p → List AExpr} (hs : c.Out (fun p x=>(as p x).map (fun a=>a.program.code))) :
    O c (fun p x=>AExpr.sum (as p x)) :=
  (hs.map p_sumCode.to_comp).ofEq (fun p x=>sumCode_eq (as p x))
lemma O.first {a : ∀p,A p → AExpr} {b : UEncoding P B} (ha : O c a) :
    O (c.prod b) (fun p x=>a p x.1) := Out.first ha
lemma O.second {a : ∀p,A p → AExpr} {b : UEncoding P B} (ha : O c a) :
    O (b.prod c) (fun p x=>a p x.2) := Out.second ha
lemma O.comp {a : ∀p,B p → AExpr} {b : UEncoding P B} {f : ∀p,A p → B p}
    (ha : O b a) (hf : c.Map b f) : O c (fun p x=>a p (f p x)) := Out.comp ha hf
lemma O.fromC {a : P → AExpr} (ha : C a) : O c (fun p _=>a p) := out_const c ha
lemma O.toC {a : P → AExpr} (ha : O (UEncoding.fixed (P:=P) Encoding.unit) (fun p _=>a p)) : C a := by
  obtain ⟨f,hf,he⟩:=ha
  exact (hf.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())

end MinUncut.Preprocess.Syntax

end
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

structure Signature (u : ℕ) where
  positive : Fin u → Slot → Bool
  same : (Fin u × Slot) → (Fin u × Slot) → Bool

def positiveAt {n : ℕ} (c : Clause n) : Slot → Bool
  | .first => (c)[0].positive
  | .second => (c)[1].positive
  | .third => (c)[2].positive

def signature (F : Formula) {u : ℕ} (c : ClauseContext F u) : Signature u where
  positive t := positiveAt (clauseAt F (c t))
  same a b := decide (nameAt (clauseAt F (c a.1)) a.2 = nameAt (clauseAt F (c b.1)) b.2)

def Signature.satisfies {u : ℕ} (S : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (S.positive t .first) (j t).first ||
    literalValue (S.positive t .second) (j t).second) ||
    literalValue (S.positive t .third) (j t).third

def Signature.valid {u : ℕ} (S : Signature u) (j : J u) : Bool :=
  decide ((∀ t, S.satisfies j t = true) ∧ ∀ t t' s s',
    S.same (t,s) (t',s') = true → answerAt (j t) s = answerAt (j t') s')

def Signature.slot {u : ℕ} (S : Signature u) (s : SlotContext u) (t : Fin u) : Slot :=
  if S.same (t,.first) (t,s t) then .first
  else if S.same (t,.second) (t,s t) then .second else .third

def Signature.project {u : ℕ} (S : Signature u) (s : SlotContext u) (j : J u) : I u :=
  fun t => answerAt (j t) (S.slot s t)

@[simp] lemma signature_valid (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (signature F c).valid = validJ F c := by
  funext j
  simp only [Signature.valid, signature, Signature.satisfies, positiveAt,
    validJ, localSatisfies, decide_eq_true_eq]
  rfl

@[simp] lemma signature_project (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (signature F c).project s = pi F c (sampledVariables F c s) := by
  funext j t
  simp only [Signature.project, Signature.slot, signature, decide_eq_true_eq,
    pi, canonicalSlot, sampledVariables]
  rfl

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)

def keyAddress (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v,f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c,g)))
  | .inr (.inr _) => dummyIndex F u

def emptyLocal {u : ℕ} : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocal {u : ℕ} (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

def localEquation {u D : ℕ} (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation emptyLocal (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocal valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀ t.1 t.2.2
        (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1))

def Signature.equation {u D : ℕ} (S : Signature u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  localEquation S.valid (S.project s) t

lemma mapEquation_comp {A B C : Type} (f : A → B) (g : B → C) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := by
  cases e
  rfl

lemma localEquation_spec (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (t : SourceTape.TestTape (I u) (J u) D) :
    mapEquation (keyAddress F c v) (localEquation (validJ F c) (pi F c v) t) =
      contextEquation F u D c v t := by
  unfold localEquation contextEquation rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    simp only
    rw [mapEquation_comp]
    congr 1
    funext a
    cases a <;> rfl
  | some j₀ =>
    simp only
    rw [mapEquation_comp]
    unfold conditionedOccurrence
    congr 1
    funext a
    cases a <;> rfl

lemma signature_equation (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceTape.TestTape (I u) (J u) D) :
    mapEquation (keyAddress F c (sampledVariables F c s))
      ((signature F c).equation s t) = sourceEquation F u D ((c,s),t) := by
  unfold Signature.equation
  rw [signature_valid, signature_project]
  exact localEquation_spec F c _ t

end MinUncut.SourceTemplate

end OAI
