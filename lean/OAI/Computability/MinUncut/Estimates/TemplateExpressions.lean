import Mathlib
import OAI.Computability.MinUncut.Search.UniformQuantifier
import OAI.Computability.MinUncut.Estimates.UniformTransport
import OAI.Computability.MinUncut.Encoding.SignatureEncoding
import OAI.Computability.MinUncut.Search.TemplateArithmetic

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def functionExpr {A : Type} (e : Encoding A) (b : ℕ) (f : A → AExpr) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin e.size => .mul (f (e.code.symm i)) (.const (b^i.val))))

lemma functionExpr_eval {A B : Type} (a : Encoding A) (b : Encoding B) (f : A → AExpr)
    (g : A → B) (v : List ℕ) (h : ∀x,(f x).eval v=(b.code (g x)).val) :
    (functionExpr a b.size f).eval v=((a.function b).code g).val := by
  simp only [functionExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,h]
  rfl

def positiveExpr (u : ℕ) : AExpr :=
  functionExpr (Encoding.fin u) (2^3) (fun i => functionExpr slotEncoding 2 (fun s=>slotWord i.val s 1))
def sameExpr (u : ℕ) : AExpr :=
  functionExpr (coordinateEncoding u) (2^(u*3)) (fun a =>
    functionExpr (coordinateEncoding u) 2 (fun b=>.eq (slotWord a.1.val a.2 0) (slotWord b.1.val b.2 0)))
def signatureExpr (u : ℕ) : AExpr :=
  .add (sameExpr u) (.mul (.const ((2^(u*3))^(u*3))) (positiveExpr u))

lemma positiveExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (positiveExpr u).eval (inputTuple F c)=
      ((((Encoding.fin u).function (slotEncoding.function Encoding.bool)).code (signature F c).positive)).val := by
  unfold positiveExpr
  apply functionExpr_eval (Encoding.fin u) (slotEncoding.function Encoding.bool)
  intro i
  apply functionExpr_eval slotEncoding Encoding.bool
  intro s
  rw [slotWord_positive,MinUncut.Outer.LocalTemplate.bool_code]
  rfl

lemma sameExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (sameExpr u).eval (inputTuple F c)=
      ((((coordinateEncoding u).function ((coordinateEncoding u).function Encoding.bool)).code (signature F c).same)).val := by
  unfold sameExpr
  apply functionExpr_eval (coordinateEncoding u) ((coordinateEncoding u).function Encoding.bool)
  intro a
  apply functionExpr_eval (coordinateEncoding u) Encoding.bool
  intro b
  simp only [AExpr.eval,slotWord_name,signature,MinUncut.Outer.LocalTemplate.bool_code]
  by_cases h : nameAt (clauseAt F (c a.1)) a.2=nameAt (clauseAt F (c b.1)) b.2
  · simp only [h,ite_true,decide_true,Bool.toNat_true]
  · have hh := Fin.val_ne_of_ne h
    simp only [hh,ite_false,h,decide_false,Bool.toNat_false]

lemma signatureExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (signatureExpr u).eval (inputTuple F c)=((signatureEncoding u).code (signature F c)).val := by
  simp only [signatureExpr,AExpr.eval,positiveExpr_eval,sameExpr_eval]
  rfl

def signatureLookup {u : ℕ} (f : Signature u → ℕ) : AExpr :=
  (signatureExpr u).lookup (MinUncut.Outer.LocalTemplate.constantTable (signatureEncoding u) f)

lemma signatureLookup_eval (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (f : Signature u → ℕ) :
    (signatureLookup f).eval (inputTuple F c)=f (signature F c) := by
  apply MinUncut.Outer.LocalTemplate.constantTable_eval
  exact signatureExpr_eval F c

def sampledExpr {u : ℕ} (s : SlotContext u) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin u=>.mul (slotWord i.val (s i) 0) ((AExpr.reg 1).pow i.val)))

lemma sampledExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) (s : SlotContext u) :
    (sampledExpr s).eval (inputTuple F c)=
      ((variableEncoding F u).code (sampledVariables F c s)).val := by
  simp only [sampledExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    AExpr.eval_pow,slotWord_name]
  rfl

def addressExpr {u : ℕ} (s : SlotContext u) (f : Signature u → LocalKey u) : AExpr :=
  let tag := signatureLookup (fun S=>keyTag (f S))
  let table := signatureLookup (fun S=>keyTable (f S))
  let leftSize := .mul ((AExpr.reg 1).pow u) (.const (2^(2^u)))
  .cond (.eq tag (.const 0))
    (.cond (.eq tag (.const 1))
      (.add leftSize (.mul ((AExpr.reg 2).pow u) (.const (2^(8^u)))))
      (.add leftSize (.add table (.mul (.const (2^(8^u))) (.reg 0)))))
    (.add table (.mul (.const (2^(2^u))) (sampledExpr s)))

lemma addressExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (f : Signature u → LocalKey u) :
    (addressExpr s f).eval (inputTuple F c)=
      (keyAddress F c (sampledVariables F c s) (f (signature F c))).val := by
  rw [keyAddress_number]
  simp only [addressExpr,AExpr.eval,signatureLookup_eval,sampledExpr_eval,AExpr.eval_pow]
  by_cases h0 : keyTag (f (signature F c))=0
  · simp only [h0,ite_true,Nat.one_ne_zero,ite_false,keyNumber]
  · by_cases h1 : keyTag (f (signature F c))=1 <;>
      simp only [h0,h1,ite_true,ite_false,Nat.one_ne_zero,keyNumber,inputTuple,
        Complexity.formulaWords,List.cons_append,List.nil_append,List.drop_succ_cons,
        List.drop_zero,List.headI_cons]

def equationExpressions {u D : ℕ} (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) : List AExpr :=
  [addressExpr s (fun S=>(S.equation s t).first),
   addressExpr s (fun S=>(S.equation s t).second),
   addressExpr s (fun S=>(S.equation s t).third),
   signatureLookup (fun S=>(S.equation s t).rhs.toNat)]

lemma equationExpressions_eval (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceTape.TestTape (I u) (J u) D) :
    (equationExpressions s t).map (fun e=>e.eval (inputTuple F c))=
      MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D ((c,s),t)) := by
  rw [←signature_equation]
  simp only [equationExpressions,List.map_cons,List.map_nil,addressExpr_eval,signatureLookup_eval]
  unfold mapEquation MinUncutGames.Reduction.SourceEncoding.equationWords
  congr 3
  cases ((signature F c).equation s t).rhs <;> rfl

end MinUncut.SourceTemplate

end
section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.FiniteProof MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type} {c : UEncoding P A}
lemma O.ofEq {f g : ∀p,A p → AExpr} (hf : O c f) (h : ∀p x,f p x=g p x) : O c g :=
  Out.ofEq hf (fun p x=>congrArg (fun a:AExpr=>a.program.code) (h p x))

def eqCode (a b : Code) : Code := branch (bin PolyProgram.add.code
  (bin PolyProgram.sub.code a b) (bin PolyProgram.sub.code b a)) (constCode 1) (constCode 0)
lemma p_eqCode : Primrec₂ eqCode := p_branch.comp
  (((p_bin _).comp ((p_bin _).comp Primrec.fst Primrec.snd)
    ((p_bin _).comp Primrec.snd Primrec.fst)).pair
    ((Primrec.const (constCode 1)).pair (Primrec.const (constCode 0))))
def lookupCode (a : Code) (xs : List (ℕ × ℕ)) : Code := xs.foldr
  (fun ix b=>branch (eqCode a (constCode ix.1)) b (constCode ix.2)) (constCode 0)
lemma p_lookupCode : Primrec₂ lookupCode := by
  exact Primrec.list_foldr Primrec.snd (Primrec.const (constCode 0))
    (p_branch.comp
      ((p_eqCode.comp (Primrec.fst.comp Primrec.fst)
        (p_constCode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))).pair
        (Primrec.snd.comp Primrec.snd |>.pair
          (p_constCode.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))).to₂
lemma lookupCode_eq (a : AExpr) (xs : List (ℕ × ℕ)) :
    lookupCode a.program.code xs=(a.lookup xs).program.code := by
  induction xs with
  | nil => rfl
  | cons ix xs ih =>
    simp only [lookupCode,List.foldr_cons] at *
    rw [ih]
    rw [AExpr.lookup,cond_code,eq_code]
    rfl
lemma O.lookup {a : ∀p,A p → AExpr} {xs : ∀p,A p → List (ℕ × ℕ)}
    (ha : O c a) (hx : c.Out xs) : O c (fun p x=>(a p x).lookup (xs p x)) :=
  (ha.map₂ hx p_lookupCode.to_comp).ofEq (fun p x=>lookupCode_eq (a p x) (xs p x))
lemma O.sum_enum {b : UEncoding P B} {f : ∀p,A p × B p → AExpr}
    (hf : O (c.prod b) f) : O c (fun p x=>AExpr.sum ((b.enc p).enumerate.map (fun y=>f p (x,y)))) := by
  apply O.sum
  apply (out_list hf).ofEq
  intro p x
  simp only [List.map_map,Function.comp_def]
lemma O.sum_fin {n : P → ℕ} (hn : Computable n) {f : ∀p,A p × Fin (n p) → AExpr}
    (hf : O (c.prod (fin n hn)) f) : O c (fun p x=>AExpr.sum (List.ofFn (fun i=>f p (x,i)))) := by
  apply hf.sum_enum.ofEq
  intro p x
  simp only [fin,Encoding.fin,Encoding.enumerate,List.map_ofFn,Function.comp_def,Equiv.refl_symm]
  rfl
lemma out_constantTable {b : UEncoding P B} {f : ∀p,A p × B p → ℕ}
    (hf : (c.prod b).Out f) : c.Out (fun p x=>MinUncut.Outer.LocalTemplate.constantTable (b.enc p) (fun y=>f p (x,y))) :=
  out_list ((out_code b).second.pair hf)
lemma O.functionExpr {b : UEncoding P B} {base : P → ℕ} (hb : Computable base)
    {f : ∀p,A p × B p → AExpr} (hf : O (c.prod b) f) :
    O c (fun p x=>MinUncut.SourceTemplate.functionExpr (b.enc p) (base p) (fun y=>f p (x,y))) := by
  have hpow : (c.prod b).Out (fun p x=>base p ^ ((b.enc p).code x.2).val) :=
    (out_const _ hb).map₂ (out_code b).second (ca_pow Computable.fst Computable.snd)
  apply (hf.mul (O.const hpow)).sum_enum.ofEq
  intro p x
  simp only [MinUncut.SourceTemplate.functionExpr,Encoding.enumerate,List.map_ofFn,Function.comp_def,Equiv.apply_symm_apply]
end MinUncut.Preprocess.Syntax

end
end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def positions : UEncoding ℕ Fin := UEncoding.fin id Computable.id
def slots : UEncoding ℕ (fun _=>Slot) := fixed slotEncoding
def answers : UEncoding ℕ (fun _=>ClauseAnswer) := fixed clauseAnswerEncoding
def lefts : UEncoding ℕ I := positions.function bool
def rights : UEncoding ℕ J := positions.function answers
def coordinates : UEncoding ℕ (fun u=>Fin u × Slot) := positions.prod slots
def polarities : UEncoding ℕ (fun u=>Fin u → Slot → Bool) := positions.function (slots.function bool)
def equalities : UEncoding ℕ (fun u=>(Fin u × Slot) → (Fin u × Slot) → Bool) :=
  coordinates.function (coordinates.function bool)
def signatures : UEncoding ℕ Signature := (polarities.prod equalities).ofEquiv signatureEquiv

lemma signatures_encoding (u : ℕ) : signatures.enc u=signatureEncoding u := rfl
lemma map_positive : signatures.Map polarities (fun _ s=>s.positive) := by
  change ((polarities.prod equalities).ofEquiv signatureEquiv).Map polarities (fun u s=>(signatureEquiv u s).1)
  exact map_comp (map_to (polarities.prod equalities) signatureEquiv) (map_fst polarities equalities)
lemma map_same : signatures.Map equalities (fun _ s=>s.same) := by
  change ((polarities.prod equalities).ofEquiv signatureEquiv).Map equalities (fun u s=>(signatureEquiv u s).2)
  exact map_comp (map_to (polarities.prod equalities) signatureEquiv) (map_snd polarities equalities)

variable {Γ : ℕ → Type} {g : UEncoding ℕ Γ}
lemma map_satisfies {s : ∀u,Γ u → Signature u} {j : ∀u,Γ u → J u} {t : ∀u,Γ u → Fin u}
    (hs : g.Map signatures s) (hj : g.Map rights j) (ht : g.Map positions t) :
    g.Map bool (fun u x=>(s u x).satisfies (j u x) (t u x)) := by
  exact map_binary (slotEncoding.function Encoding.bool) clauseAnswerEncoding Encoding.bool
    (fun p a=>(literalValue (p .first) a.first || literalValue (p .second) a.second) ||
      literalValue (p .third) a.third)
    (map_apply (map_comp hs map_positive) ht) (map_apply hj ht)

lemma map_same_at {s : ∀u,Γ u → Signature u} {a b : ∀u,Γ u → Fin u × Slot}
    (hs : g.Map signatures s) (ha : g.Map coordinates a) (hb : g.Map coordinates b) :
    g.Map bool (fun u x=>(s u x).same (a u x) (b u x)) :=
  map_apply (map_apply (map_comp hs map_same) ha) hb
lemma map_answer_at {j : ∀u,Γ u → J u} {a : ∀u,Γ u → Fin u × Slot}
    (hj : g.Map rights j) (ha : g.Map coordinates a) :
    g.Map bool (fun u x=>answerAt (j u x (a u x).1) (a u x).2) :=
  map_binary clauseAnswerEncoding slotEncoding Encoding.bool answerAt
    (map_apply hj (map_comp ha (map_fst _ _))) (map_comp ha (map_snd _ _))

lemma map_consistent {s : ∀u,Γ u → Signature u} {j : ∀u,Γ u → J u}
    {a b : ∀u,Γ u → Fin u × Slot}
    (hs : g.Map signatures s) (hj : g.Map rights j)
    (ha : g.Map coordinates a) (hb : g.Map coordinates b) :
    g.Map bool (fun u x=>decide ((s u x).same (a u x) (b u x)=true →
      answerAt (j u x (a u x).1) (a u x).2=answerAt (j u x (b u x).1) (b u x).2)) := by
  apply (map_or (map_not (map_same_at hs ha hb))
    (map_bool_eq (map_answer_at hj ha) (map_answer_at hj hb))).ofEq
  intro u x
  by_cases h:(s u x).same (a u x) (b u x)=true <;> simp [h]

lemma map_valid : (signatures.prod rights).Map bool (fun _ x=>x.1.valid x.2) := by
  classical
  have hs : ((signatures.prod rights).prod positions).Map bool
      (fun u x=>x.1.1.satisfies x.1.2 x.2) :=
    map_satisfies (map_fst signatures rights).first (map_snd signatures rights).first (map_snd _ _)
  have hc : (((signatures.prod rights).prod coordinates).prod coordinates).Map bool
      (fun u x=>decide (x.1.1.1.same x.1.2 x.2=true →
        answerAt (x.1.1.2 x.1.2.1) x.1.2.2=answerAt (x.1.1.2 x.2.1) x.2.2)) :=
    map_consistent (map_fst signatures rights).first.first (map_snd signatures rights).first.first
      (map_snd (signatures.prod rights) coordinates).first (map_snd _ _)
  apply (map_and (map_forall hs) (map_forall (map_forall hc))).ofEq
  intro u x
  simp only [Signature.valid,Bool.decide_and,decide_eq_true_eq]
  congr 1
  apply decide_eq_decide.mpr
  simp only [Prod.forall]
  constructor
  · intro h t t' s s' he
    exact h t s t' s' he
  · intro h t s t' s' he
    exact h t t' s s' he

end MinUncut.Preprocess.Source

end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def slotContexts : UEncoding ℕ SlotContext := positions.function slots

variable {Γ : ℕ → Type} {g : UEncoding ℕ Γ}
lemma map_slot {s : ∀u,Γ u → Signature u} {r : ∀u,Γ u → SlotContext u} {t : ∀u,Γ u → Fin u}
    (hs : g.Map signatures s) (hr : g.Map slotContexts r) (ht : g.Map positions t) :
    g.Map slots (fun u x=>(s u x).slot (r u x) (t u x)) := by
  exact map_binary Encoding.bool Encoding.bool slotEncoding
    (fun b c=>if b then .first else if c then .second else .third)
    (map_same_at hs (map_pair ht (map_const (Computable.const 0))) (map_pair ht (map_apply hr ht)))
    (map_same_at hs (map_pair ht (map_const (Computable.const 1))) (map_pair ht (map_apply hr ht)))

lemma map_project {s : ∀u,Γ u → Signature u} {r : ∀u,Γ u → SlotContext u} {j : ∀u,Γ u → J u}
    (hs : g.Map signatures s) (hr : g.Map slotContexts r) (hj : g.Map rights j) :
    g.Map lefts (fun u x=>(s u x).project (r u x) (j u x)) := by
  exact map_lambda (map_binary clauseAnswerEncoding slotEncoding Encoding.bool answerAt
    (map_apply hj.first (map_snd g positions))
    (map_slot hs.first hr.first (map_snd g positions)))

lemma map_anchor (a : UEncoding ℕ Γ) : a.Map lefts (fun u _=>leftAnchor u) :=
  map_lambda (map_false (a.prod positions))

end MinUncut.Preprocess.Source

namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad
variable {P : Type} [Primcodable P] {A Γ : P → Type}
lemma map_xor {g : UEncoding P Γ} {f h : ∀p,Γ p → Bool}
    (hf : g.Map bool f) (hh : g.Map bool h) : g.Map bool (fun p x=>f p x ^^ h p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.xor hf hh

lemma map_representative {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p → A p → Bool} {i : ∀p,Γ p → A p}
    (hf : g.Map (a.function bool) f) (hi : g.Map a i) :
    g.Map (a.function bool) (fun p x=>representative (i p x) (f p x)) := by
  apply (map_lambda (map_xor (map_apply hf.first (map_snd g a)) (map_apply hf hi).first)).ofEq
  intro p x
  funext y
  change (f p x y ^^ f p x (i p x))=(if f p x (i p x) then cubeFlip (f p x) else f p x) y
  cases f p x (i p x) <;> simp [cubeFlip]
end MinUncut.Preprocess.UEncoding

end
section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

def paddedRep {u : ℕ} (valid : J u → Bool) (j₀ : J u) (g : Cube (J u)) : Cube (J u) :=
  fun j=>if valid j then representative j₀ g j else false

lemma extend_representative {u : ℕ} (valid : J u → Bool)
    (j₀ : {j : J u // valid j=true}) (g : Cube (J u)) :
    extendRestricted valid (representative j₀ (restrictQuery valid g))=paddedRep valid j₀ g := by
  funext j
  unfold extendRestricted paddedRep
  by_cases h:valid j=true
  · simp only [h,↓reduceDIte,ite_true]
    cases h₀:g j₀ <;> simp [representative,restrictQuery,cubeFlip,h₀]
  · simp [h]

lemma findValid_map {X : Type} (valid : X → Bool) (xs : List X) :
    (findValid valid xs).map Subtype.val=xs.find? valid := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h:valid x=true <;> simp [findValid,h,ih]

def rawLocal {u : ℕ} (valid : J u → Bool) (π : J u → I u)
    (f : Cube (I u)) (g μ : Cube (J u)) : Equation (LocalKey u) :=
  ((jEncoding u).enumerate.find? valid).elim
    ⟨.inl (representative (leftAnchor u) f),.inr (.inr ()),.inr (.inr ()),f (leftAnchor u)⟩
    (fun j₀=>⟨.inl (representative (leftAnchor u) f),
      .inr (.inl (paddedRep valid j₀ g)),
      .inr (.inl (paddedRep valid j₀ (thirdQuery π f g μ))),
      f (leftAnchor u) ^^ f (π j₀) ^^ μ j₀⟩)

lemma rawLocal_eq {u D : ℕ} (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    rawLocal valid π t.1 t.2.2 (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1)=
      localEquation valid π t := by
  rw [rawLocal,←findValid_map,←firstValid]
  unfold localEquation
  cases hh:firstValid (jEncoding u) valid with
  | none => rfl
  | some j₀ =>
    dsimp only [Option.map_some,Option.elim_some,mapEquation,FoldedEquation.conditionedEquation,
      FoldedEquation.equation,foldedLocal,canonicalInput]
    rw [extend_representative]
    have he : thirdQuery (fun j:{j : J u // valid j=true}=>π j.val) t.1
        (restrictQuery valid t.2.2)
        (restrictQuery valid (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1))=
        restrictQuery valid (thirdQuery π t.1 t.2.2
          (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1)) := rfl
    rw [he,extend_representative]
    rfl
end MinUncut.SourceTemplate

end

end OAI
