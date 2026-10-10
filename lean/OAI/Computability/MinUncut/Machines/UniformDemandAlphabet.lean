import Mathlib
import OAI.Computability.MinUncut.Search.UniformQuantifier
import OAI.Computability.MinUncut.Encoding.SignatureEncoding
import OAI.Computability.MinUncut.Machines.UniformAlphabet

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
attribute [local instance] Classical.propDecidable
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
def triples : UEncoding P (fun _=>Triple) := (positions (P:=P)).function (field P)
def ambient := (axes t ht).function (triples (P:=P))
def positionsList := (axes t ht).function (positions (P:=P))
def rhs := (axes t ht).function (field P)
def equalities := (axes t ht).function ((positions (P:=P)).function ((positions (P:=P)).function bool))
def signatures : UEncoding P (fun p=>Signature (Fin (t p))) :=
  ((rhs t ht).prod (equalities t ht)).ofEquiv (fun p=>signatureEquiv (t p))
lemma signatures_encoding (p : P) : (signatures t ht).enc p=signatureEncoding (t p) := rfl
lemma ambient_encoding (p : P) : (ambient t ht).enc p=ambientEncoding (t p) := rfl
lemma map_rhs : (signatures t ht).Map (rhs t ht) (fun _ s=>s.rhs) := by
  have hh := map_comp (map_to ((rhs t ht).prod (equalities t ht)) (fun p=>signatureEquiv (t p)))
    (map_fst (rhs t ht) (equalities t ht))
  exact hh
lemma map_same : (signatures t ht).Map (equalities t ht) (fun _ s=>s.same) := by
  have hh := map_comp (map_to ((rhs t ht).prod (equalities t ht)) (fun p=>signatureEquiv (t p)))
    (map_snd (rhs t ht) (equalities t ht))
  exact hh
lemma map_origin : (signatures t ht).Map (ambient t ht) (fun _ s=>s.origin) := by
  let c:=signatures t ht
  let ax:=axes t ht
  let po:=positions (P:=P)
  have hh : ((c.prod ax).prod po).Map (field P) (fun _ x=>x.1.1.rhs x.1.2) :=
    map_apply (map_rhs t ht).first.first (map_snd c ax).first
  exact map_lambda (map_lambda hh)
lemma map_zeroLabel : (fixed (P:=P) Encoding.unit).Map (labels t ht h hc) (fun _ _=>0) := by
  let s:=slots t ht h hc
  have hf : (fixed (P:=P) Encoding.unit).Map (s.function (field P)) (fun _ _ _=>0) :=
    map_lambda (map_const (Computable.const 0))
  have hh := map_comp hf (map_from (s.function (field P)) (labelEquiv t h))
  exact hh
lemma map_slotCoords : (slots t ht h hc).Map (slotPairs t ht)
    (fun _ x=>((slotEquiv t h _ x).val)) :=
  map_comp (map_to _ (slotEquiv t h)) (map_restrict_val _ _ (map_slotGood t ht h hc))
lemma projectSlot_apply (b : Bool) (pos : Fin 3) (x : Triple) (k : Fin (width b))
    (hk : k.val<3) : projectSlot b pos x k = if b then x pos else x ⟨k.val,hk⟩ := by
  cases b <;> rfl
lemma map_slotAxis : (slots t ht h hc).Map (axes t ht) (fun _ x=>x.1) := by
  have hh := map_comp (map_slotCoords t ht h hc) (map_fst (axes t ht) (positions (P:=P)))
  exact hh
lemma map_slotPosition : (slots t ht h hc).Map (positions (P:=P))
    (fun p x=>(slotEquiv t h p x).val.2) := by
  have hh := map_comp (map_slotCoords t ht h hc) (map_snd (axes t ht) (positions (P:=P)))
  exact hh
lemma map_projectEval : (((positionsList t ht).prod (ambient t ht)).prod (slots t ht h hc)).Map
    (field P) (fun p x=>project (h p) x.1.1 x.1.2 x.2.1 x.2.2) := by
  let c:=(positionsList t ht).prod (ambient t ht)
  let sl:=slots t ht h hc
  let ax:=axes t ht
  let po:=positions (P:=P)
  have hi : (c.prod sl).Map ax (fun _ x=>x.2.1) := (map_slotAxis t ht h hc).second
  have hk : (c.prod sl).Map po (fun p x=>(slotEquiv t h p x.2).val.2) := (map_slotPosition t ht h hc).second
  have hpos : (c.prod sl).Map po (fun _ x=>x.1.1 x.2.1) :=
    map_apply (map_fst _ _).first hi
  have hm : (c.prod sl).Map (ax.function bool) (fun p _=>h p) := map_const hc
  have hh : (c.prod sl).Map bool (fun p x=>h p x.2.1) := map_apply hm hi
  have hx : (c.prod sl).Map (triples (P:=P)) (fun _ x=>x.1.2 x.2.1) :=
    map_apply (map_snd _ _).first hi
  apply (map_cond hh (map_apply hx hpos) (map_apply hx hk)).ofEq
  intro p x
  exact (projectSlot_apply _ _ _ _ _).symm
lemma map_project : ((positionsList t ht).prod (ambient t ht)).Map (labels t ht h hc)
    (fun p x=>project (h p) x.1 x.2) := by
  let c:=(positionsList t ht).prod (ambient t ht)
  let sl:=slots t ht h hc
  have hl : c.Map (sl.function (field P)) (fun p x y=>project (h p) x.1 x.2 y.1 y.2) :=
    map_lambda (map_projectEval t ht h hc)
  have hout := map_comp hl (map_from (sl.function (field P)) (labelEquiv t h))
  exact hout.ofEq (by intro p x; rfl)
lemma map_decode : (ambient t ht).Map (labels t ht h hc) (fun p x=>decode (h p) x) := by
  have hz : (ambient t ht).Map (positionsList t ht) (fun _ _ _=>0) :=
    map_lambda (map_const (Computable.const 0))
  have hh := map_comp (map_pair hz (map_id _)) (map_project t ht h hc)
  exact hh
lemma map_valid : ((signatures t ht).prod (ambient t ht)).Map bool
    (fun _ x=>decide (x.1.Valid x.2)) := by
  classical
  let c:=(signatures t ht).prod (ambient t ht)
  let ax:=axes t ht
  let po:=positions (P:=P)
  let tr:=triples (P:=P)
  have hx : (c.prod ax).Map tr (fun _ x=>x.1.2 x.2) :=
    map_apply (map_snd _ _).first (map_snd c ax)
  have hr : (c.prod ax).Map (field P) (fun _ x=>x.1.1.rhs x.2) :=
    map_apply (map_rhs t ht).first.first (map_snd c ax)
  have hpar : (c.prod ax).Map (field P) (fun _ x=>parity (x.1.2 x.2)) :=
    map_fixed_apply ((Encoding.fin 3).function fieldEncoding) fieldEncoding parity hx
  have hsame : (((c.prod ax).prod po).prod po).Map bool
      (fun _ x=>x.1.1.1.1.same x.1.1.2 x.1.2 x.2) :=
    map_apply (map_apply (map_apply (map_same t ht).first.first.first.first
      (map_snd c ax).first.first) (map_snd (c.prod ax) po).first) (map_snd _ _)
  have hp : (((c.prod ax).prod po).prod po).Map (field P)
      (fun _ x=>x.1.1.1.2 x.1.1.2 x.1.2) :=
    map_apply hx.first.first (map_snd (c.prod ax) po).first
  have hq : (((c.prod ax).prod po).prod po).Map (field P)
      (fun _ x=>x.1.1.1.2 x.1.1.2 x.2) :=
    map_apply hx.first.first (map_snd _ _)
  have he:=map_forall (map_forall (map_or (map_not hsame) (map_bool_eq hp hq)))
  apply (map_forall (map_and (map_bool_eq hpar hr) he)).ofEq
  intro p x
  simp only [Signature.Valid,decide_eq_true_eq]
  apply decide_eq_decide.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true',Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro H i
    refine ⟨(H i).1,?_⟩
    intro j k hj
    rcases (H i).2 j k with h|h
    · simp [hj] at h
    · exact h
  · intro H i
    refine ⟨(H i).1,?_⟩
    intro j k
    by_cases hj:x.1.same i j k=true
    · exact Or.inr ((H i).2 j k hj)
    · exact Or.inl (Bool.eq_false_iff.mpr hj)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
