import Mathlib
import OAI.Computability.MinUncut.Search.UniformFind
import OAI.Computability.MinUncut.Estimates.UniformAlgebra
import OAI.Computability.MinUncut.Analysis.UniformCube

namespace OAI

namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.SourceTemplate UEncoding

abbrev Par := ℕ × ℕ
abbrev up {A : ℕ → Type} (a : UEncoding ℕ A) : UEncoding Par (fun p=>A p.1) := a.pullback Prod.fst Computable.fst

def ls : UEncoding Par (fun p=>I p.1) := up lefts
def rs : UEncoding Par (fun p=>J p.1) := up rights
def fc := ls.function bool
def gc := rs.function bool
def keys : UEncoding Par (fun p=>LocalKey p.1) := fc.sum (gc.sum (fixed Encoding.unit))

variable {Γ : Par → Type} {e : UEncoding Par Γ}
lemma map_rawLocal {v : ∀p,Γ p → J p.1 → Bool} {π : ∀p,Γ p → J p.1 → I p.1}
    {f : ∀p,Γ p → Cube (I p.1)} {g μ : ∀p,Γ p → Cube (J p.1)}
    (hv : e.Map gc v) (hπ : e.Map (rs.function ls) π)
    (hf : e.Map fc f) (hg : e.Map gc g) (hμ : e.Map gc μ) :
    e.Map keys.equation (fun p x=>rawLocal (v p x) (π p x) (f p x) (g p x) (μ p x)) := by
  have ha : e.Map ls (fun p _=>leftAnchor p.1) :=
    map_lambda (map_false (e.prod (up positions)))
  have hfirst := map_comp (map_representative hf ha) (map_inl fc (gc.sum (fixed Encoding.unit)))
  have hdummy : e.Map keys (fun _ _=>Sum.inr (Sum.inr ())) :=
    map_comp (map_comp (map_const (Computable.const 0)) (map_inr gc (fixed Encoding.unit)))
      (map_inr fc (gc.sum (fixed Encoding.unit)))
  have hnone : e.Map keys.equation (fun p x=>
      ⟨.inl (representative (leftAnchor p.1) (f p x)),.inr (.inr ()),.inr (.inr ()),f p x (leftAnchor p.1)⟩) :=
    map_equation hfirst hdummy hdummy (map_apply hf ha)
  have hright (h : e.Map gc g) : (e.prod rs).Map keys
      (fun p x=>.inr (.inl (paddedRep (v p x.1) x.2 (g p x.1)))) :=
    map_comp (map_comp (map_padded hv.first h.first (map_snd e rs))
      (map_inl gc (fixed Encoding.unit))) (map_inr fc (gc.sum (fixed Encoding.unit)))
  have hthird := map_thirdQuery hπ hf hg hμ
  have hsome : (e.prod rs).Map keys.equation (fun p x=>
      ⟨.inl (representative (leftAnchor p.1) (f p x.1)),
       .inr (.inl (paddedRep (v p x.1) x.2 (g p x.1))),
       .inr (.inl (paddedRep (v p x.1) x.2 (thirdQuery (π p x.1) (f p x.1) (g p x.1) (μ p x.1)))),
       f p x.1 (leftAnchor p.1) ^^ f p x.1 (π p x.1 x.2) ^^ μ p x.1 x.2⟩) := by
    exact map_equation hfirst.first (hright hg)
      (map_comp (map_comp (map_padded hv.first hthird.first (map_snd e rs))
        (map_inl gc (fixed Encoding.unit))) (map_inr fc (gc.sum (fixed Encoding.unit))))
      (map_xor (map_xor (map_apply hf ha).first
         (map_apply hf.first (map_apply hπ.first (map_snd e rs))))
         (map_apply hμ.first (map_snd e rs)))
  apply (map_comp (map_pair (map_id e) (map_find_apply hv)) (map_option_elim hnone hsome)).ofEq
  intro p x
  rfl

def ds : UEncoding Par (fun p=>Fin p.2) := fin Prod.snd Computable.snd
def tapes : UEncoding Par (fun p=>SourceTape.TestTape (I p.1) (J p.1) p.2) :=
  fc.prod ((rs.function ds).prod gc)
def sigs := up signatures
def sls := up slotContexts
def context := (sigs.prod sls).prod tapes

lemma map_context_signature : context.Map sigs (fun _ x=>x.1.1) :=
  (map_fst sigs sls).first
lemma map_context_slot : context.Map sls (fun _ x=>x.1.2) :=
  (map_snd sigs sls).first
lemma map_context_first : context.Map fc (fun _ x=>x.2.1) :=
  map_comp (map_snd _ _) (map_fst _ _)
lemma map_context_last : context.Map gc (fun _ x=>x.2.2.2) :=
  ((map_snd (rs.function ds) gc).second (c:=fc)).second (c:=sigs.prod sls)
lemma map_context_noiseTape : context.Map (rs.function ds) (fun _ x=>x.2.2.1) :=
  ((map_fst (rs.function ds) gc).second (c:=fc)).second (c:=sigs.prod sls)
lemma map_context_valid : context.Map gc (fun _ x=>x.1.1.valid) :=
  map_lambda (map_comp (map_pair map_context_signature.first (map_snd context rs))
    (map_valid.pullback Computable.fst))
lemma map_context_project : context.Map (rs.function ls) (fun _ x=>x.1.1.project x.1.2) := by
  have hh := (map_project (g:=((signatures.prod slotContexts).prod rights))
    (map_fst signatures slotContexts).first
    (map_snd signatures slotContexts).first (map_snd _ _)).pullback
    (f:=(Prod.fst : Par → ℕ)) Computable.fst
  exact map_lambda (map_comp
    (map_pair (map_pair map_context_signature.first map_context_slot.first) (map_snd context rs)) hh)
lemma map_context_noise : context.Map gc
    (fun _ x=>MinUncutGames.Reduction.FiniteNoise.realizedNoise x.2.2.1) :=
  map_lambda (map_value_zero (map_apply map_context_noiseTape.first (map_snd context rs)))
lemma map_localEquation : context.Map keys.equation
    (fun _ x=>x.1.1.equation x.1.2 x.2) := by
  apply (map_rawLocal map_context_valid map_context_project map_context_first
    map_context_last map_context_noise).ofEq
  intro p x
  exact rawLocal_eq x.1.1.valid (x.1.1.project x.1.2) x.2
end MinUncut.Preprocess.Source

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type} {c : UEncoding P A}
lemma C.precomp {a : Q → AExpr} (ha : C a) {f : P → Q} (hf : Computable f) : C (fun p=>a (f p)) :=
  Computable.comp ha hf
lemma O.tupleDigit {i : ∀p,A p → ℕ} (hi : c.Out i) : O c (fun p x=>tupleDigit (i p x)) :=
  ((O.fixed (.reg 0)).div ((O.fixed (.reg 2)).pow hi)).mod (O.fixed (.reg 2))
lemma O.slotWord {i j : ∀p,A p → ℕ} {s : ∀p,A p → Slot}
    (hi : c.Out i) (hs : c.Map (UEncoding.fixed slotEncoding) s) (hj : c.Out j) :
    O c (fun p x=>slotWord (i p x) (s p x) (j p x)) := by
  have hn := (out_code (UEncoding.fixed (P:=P) slotEncoding)).comp hs
  have hc := (out_const c (Computable.const 2)).map₂ hn (ca_mul Computable.fst Computable.snd)
  have hb := hc.map₂ hj (ca_add Computable.fst Computable.snd)
  exact ((O.fixed (.const 3)).add ((O.fixed (.const 6)).mul (O.tupleDigit hi))).add (.const hb) |>.at

abbrev unitN : UEncoding ℕ (fun _=>Unit) := UEncoding.fixed Encoding.unit
lemma c_positiveExpr : C positiveExpr := by
  have hi : ((unitN.prod Source.positions).prod Source.slots).Out (fun _ x=>x.1.2.val) :=
    (out_code Source.positions).second.first
  have hs := map_snd (unitN.prod Source.positions) Source.slots
  have hw := O.slotWord hi hs (out_const _ (Computable.const 1))
  exact (hw.functionExpr (Computable.const 2) |>.functionExpr (Computable.const (2^3))).toC
lemma c_sameExpr : C sameExpr := by
  let c := (unitN.prod Source.coordinates).prod Source.coordinates
  have ha : c.Map Source.coordinates (fun _ x=>x.1.2) := (map_snd unitN Source.coordinates).first
  have hb : c.Map Source.coordinates (fun _ x=>x.2) := map_snd _ _
  have hai := (out_code Source.positions).comp (map_comp ha (map_fst _ _))
  have hbi := (out_code Source.positions).comp (map_comp hb (map_fst _ _))
  have has := map_comp ha (map_snd _ _)
  have hbs := map_comp hb (map_snd _ _)
  have hzero := out_const c (Computable.const 0)
  have hw := (O.slotWord hai has hzero).eq (O.slotWord hbi hbs hzero)
  exact (hw.functionExpr (Computable.const 2) |>.functionExpr
    (ca_pow (Computable.const 2) (ca_mul Computable.id (Computable.const 3)))).toC
lemma c_signatureExpr : C signatureExpr := by
  have hconst := C.const (ca_pow (ca_pow (Computable.const 2)
    (ca_mul Computable.id (Computable.const 3))) (ca_mul Computable.id (Computable.const 3)))
  exact c_sameExpr.add (hconst.mul c_positiveExpr)
lemma O.sourceLookup {u : P → ℕ} (hu : Computable u)
    {f : ∀p,A p × Signature (u p) → ℕ}
    (hf : (c.prod (Source.signatures.pullback u hu)).Out f) :
    O c (fun p x=>signatureLookup (fun s=>f p (x,s))) :=
  (O.fromC (c_signatureExpr.precomp hu)).lookup (out_constantTable hf)
lemma map_sourceSlot {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s) :
    (c.prod (fin u hu)).Map (fixed slotEncoding) (fun p x=>s p x.1 x.2) := by
  have ht : c.Map ((fin u hu).function (fixed slotEncoding)) s := hs
  exact map_apply ht.first (map_snd c (fin u hu))
lemma O.sourceSampled {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s) : O c (fun p x=>sampledExpr (s p x)) := by
  let d := c.prod (fin u hu)
  have hi : d.Out (fun _ x=>x.2.val) := (out_code (fin u hu)).second
  have hx := map_sourceSlot hu hs
  have hw : O d (fun p x=>MinUncut.SourceTemplate.slotWord x.2.val (s p x.1 x.2) 0) :=
    O.slotWord hi hx (out_const d (Computable.const 0))
  have hp : O d (fun _ x=>(AExpr.reg 1).pow x.2.val) := (O.fixed (.reg 1)).pow hi
  have hh : O d (fun p x=>.mul (MinUncut.SourceTemplate.slotWord x.2.val (s p x.1 x.2) 0) ((AExpr.reg 1).pow x.2.val)) := hw.mul hp
  exact hh.sum_fin hu
end MinUncut.Preprocess.Syntax

namespace MinUncut.Preprocess.Face
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def axes := fin m hm
def values := fin n hn
def points := (axes m hm).function (values n hn)
def rowPairs := (axes m hm).prod (points m n hm hn)
def rowGood (p : P) (x : Fin (m p) × Point (m p) (n p)) : Bool :=
  decide (x.2 x.1=⟨0,hnpos p⟩)
lemma map_rowGood : (rowPairs m n hm hn).Map bool (rowGood m n hnpos) := by
  exact map_bool_eq
    (map_apply (map_snd (axes m hm) (points m n hm hn)) (map_fst _ _))
    (map_const (Computable.const 0))

def rowEquiv (p : P) : Row (m p) (n p) ≃
    {x:Fin (m p) × Point (m p) (n p) // rowGood m n hnpos p x=true} where
  toFun r := ⟨(r.1,fun j=>if h:j=r.1 then ⟨0,hnpos p⟩ else r.2 ⟨j,h⟩),by simp [rowGood]⟩
  invFun r := ⟨r.val.1,fun j=>r.val.2 j.val⟩
  left_inv r := by
    dsimp only
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    funext j
    exact dite_eq_right j.property
  right_inv r := by
    apply Subtype.ext
    dsimp only
    refine Prod.ext (by rfl) ?_
    funext j
    by_cases h:j=r.val.1
    · subst j
      dsimp only
      split
      · exact ((of_decide_eq_true r.property) : r.val.2 r.val.1=⟨0,hnpos p⟩).symm
      · rename_i hh; exact False.elim (hh rfl)
    · exact dite_eq_right h

def rows : UEncoding P (fun p=>Row (m p) (n p)) :=
  ((rowPairs m n hm hn).restrict (rowGood m n hnpos) (map_rowGood m n hm hn hnpos)).ofEquiv
    (rowEquiv m n hnpos)

lemma map_faceRow : ((points m n hm hn).prod (axes m hm)).Map (rows m n hm hn hnpos)
    (fun _ x=>⟨x.2,face x.1 x.2⟩) := by
  let pt:=points m n hm hn
  let ax:=axes m hm
  let rs:=rowPairs m n hm hn
  let c:=pt.prod ax
  have hi : c.Map ax (fun _ x=>x.2) := map_snd _ _
  have hx : c.Map pt (fun _ x=>x.1) := map_fst _ _
  have hy : (c.prod ax).Map ax (fun _ x=>x.2) := map_snd _ _
  have hz : (c.prod ax).Map (values n hn) (fun p _=>⟨0,hnpos p⟩) := map_const (Computable.const 0)
  have hw : (c.prod ax).Map (values n hn)
      (fun p x=>if x.2=x.1.2 then ⟨0,hnpos p⟩ else x.1.1 x.2) := by
    apply (map_cond (map_bool_eq hy hi.first) hz
      (map_apply hx.first hy)).ofEq
    intro p x
    simp only [decide_eq_true_eq]
  have hp := map_pair hi (map_lambda hw)
  have hg : ∀p (x : Point (m p) (n p) × Fin (m p)),rowGood m n hnpos p (x.2,fun j=>if j=x.2 then ⟨0,hnpos p⟩ else x.1 j)=true := by
    intro p x
    simp [rowGood]
  have hmk:=map_restrict_mk (map_rowGood m n hm hn hnpos) hp hg
  apply (map_comp hmk (map_from _ (rowEquiv m n hnpos))).ofEq
  intro p x
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext j
  exact ite_eq_right j.property

lemma map_faceSum : ((rows m n hm hn hnpos).function (field P)).Map
    ((points m n hm hn).function (field P)) (fun p x=>faceSum (m p) (n p) x) := by
  let r:=rows m n hm hn hnpos
  let v:=points m n hm hn
  let ax:=axes m hm
  let c:=(r.function (field P)).prod v
  have hx : (c.prod ax).Map v (fun _ x=>x.1.2) := (map_snd _ _).first
  have hi : (c.prod ax).Map ax (fun _ x=>x.2) := map_snd _ _
  have hr : (c.prod ax).Map r (fun _ x=>⟨x.2,face x.1.2 x.2⟩) :=
    map_comp (map_pair hx hi) (map_faceRow m n hm hn hnpos)
  have hf : (c.prod ax).Map (r.function (field P)) (fun _ x=>x.1.1) := (map_fst _ _).first
  exact map_lambda (map_field_sum (map_apply hf hr))

def codeGood (p : P) (x : Point (m p) (n p) → F₂) : Bool :=
  decide (∃f:Row (m p) (n p) → F₂,faceSum (m p) (n p) f=x)
include hnpos in
lemma map_codeGood : ((points m n hm hn).function (field P)).Map bool (codeGood m n) := by
  let r:=(rows m n hm hn hnpos).function (field P)
  let v:=(points m n hm hn).function (field P)
  have hh:=map_exists (map_bool_eq
    ((map_faceSum m n hm hn hnpos).second (c:=v)) (map_fst v r))
  apply hh.ofEq
  intro p x
  simp only [codeGood,decide_eq_true_eq]

def codeEquiv (p : P) : Code (m p) (n p) ≃
    {x:Point (m p) (n p) → F₂ // codeGood m n p x=true} where
  toFun x := ⟨x.val,by simpa only [codeGood,decide_eq_true_eq] using (LinearMap.mem_range.mp x.property)⟩
  invFun x := ⟨x.val,LinearMap.mem_range.mpr (by simpa only [codeGood,decide_eq_true_eq] using x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def codes : UEncoding P (fun p=>Code (m p) (n p)) :=
  (((points m n hm hn).function (field P)).restrict (codeGood m n)
    (map_codeGood m n hm hn hnpos)).ofEquiv (codeEquiv m n)
lemma map_codeVal : (codes m n hm hn hnpos).Map ((points m n hm hn).function (field P))
    (fun _ x=>x.val) := by
  have hh := map_comp (map_to (((points m n hm hn).function (field P)).restrict (codeGood m n)
    (map_codeGood m n hm hn hnpos)) (codeEquiv m n))
    (map_restrict_val ((points m n hm hn).function (field P)) (codeGood m n)
      (map_codeGood m n hm hn hnpos))
  exact hh.ofEq (by intros; rfl)
lemma map_codeMk {Γ : P → Type} {g : UEncoding P Γ}
    {f : ∀p,Γ p → Point (m p) (n p) → F₂}
    (hf : g.Map ((points m n hm hn).function (field P)) f)
    (h : ∀p x,∃a:Row (m p) (n p) → F₂,faceSum (m p) (n p) a=f p x) :
    g.Map (codes m n hm hn hnpos) (fun p x=>⟨f p x,LinearMap.mem_range.mpr (h p x)⟩) := by
  have hh:=map_restrict_mk (map_codeGood m n hm hn hnpos) hf
    (by intro p x; simp only [codeGood,decide_eq_true_eq]; exact h p x)
  exact map_comp hh (map_from _ (codeEquiv m n))

end MinUncut.Preprocess.Face

end

end OAI
