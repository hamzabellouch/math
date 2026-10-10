import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformAlgebra

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]
  {A : P → Type} [∀p,Fintype (A p)]
lemma computable_sum {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f)
    (hadd : Computable₂ (fun x y : X=>x+y)) : Computable (fun p=>∑x,f p x) := by
  have hh:=out_sum (g:=fixed Encoding.unit) hf.second hadd
  obtain ⟨h,hr,he⟩:=hh
  exact (hr.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())
end MinUncut.Preprocess.UEncoding

end
section
namespace MinUncut.Preprocess

variable {α β : Type} [Primcodable α] [Primcodable β]

def decodeGood (dec : ℕ → Option β) (p : α → β → Prop) (x : α) (n : ℕ) : Prop :=
  (dec n).elim False (p x)

instance {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p] (x : α) (n : ℕ) :
    Decidable (decodeGood dec p x n) := by
  unfold decodeGood
  cases dec n <;> simp only [Option.elim] <;> infer_instance

lemma c_searchProj : Computable (fun q : (α × ℕ) × β=>(q.1.1,q.2)) :=
  (Computable.fst.comp Computable.fst).pair Computable.snd
lemma c_searchEval {p : α → β → Prop} [DecidableRel p]
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    Computable (fun q : (α × ℕ) × β=>decide (p q.1.1 q.2)) :=
  by
  have hh : Computable (fun q : α × β=>decide (p q.1 q.2)) := hp.decide
  exact @Computable.comp ((α × ℕ) × β) (α × β) Bool _ _ _
    (fun q=>decide (p q.1 q.2)) (fun q=>(q.1.1,q.2)) hh c_searchProj
lemma c_searchDecode {dec : ℕ → Option β} (hd : Computable dec) :
    Computable (fun q : α × ℕ=>dec q.2) := hd.comp Computable.snd
lemma c_searchBool {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p]
    (hd : Computable dec) (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    Computable (fun q : α × ℕ=>(dec q.2).elim false (fun b=>decide (p q.1 b))) :=
  (Computable.option_casesOn (c_searchDecode hd) (ca_const false) ((c_searchEval hp).to₂)).of_eq
    (fun q=>by cases dec q.2 <;> rfl)
omit [Primcodable α] [Primcodable β] in
lemma searchBool_eq {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p] (q : α × ℕ) :
    (dec q.2).elim false (fun b=>decide (p q.1 b))=decide (decodeGood dec p q.1 q.2) := by
  cases he : dec q.2 <;> simp only [decodeGood,he,Option.elim,decide_false]
lemma computable_decodeGood {dec : ℕ → Option β} {p : α → β → Prop}
    [DecidableRel p] (hd : Computable dec)
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    ComputablePred (fun q : α × ℕ=>decodeGood dec p q.1 q.2) :=
  ⟨inferInstance,(c_searchBool hd hp).of_eq searchBool_eq⟩

instance option_elim_decidable {p : β → Prop} [DecidablePred p] (o : Option β) :
    Decidable (o.elim False p) := by
  cases o <;> simp only [Option.elim] <;> infer_instance

lemma choose_getD {γ : Type} [Encodable γ] {p : γ → Prop} [DecidablePred p] (h : ∃b,p b) (d : γ) :
    Encodable.choose h =
      ((Encodable.decode (α:=γ) (Nat.find (show ∃n,(Encodable.decode (α:=γ) n).elim False p from by
        obtain ⟨b,hb⟩:=h
        exact ⟨Encodable.encode b,by simp [hb]⟩)))).getD d := by
  unfold Encodable.choose
  conv_lhs => arg 1; whnf
  split
  next oldPredicate decoded valid value validValue equation compatibility =>
    have decodedValue : (Encodable.decode (α := γ) (Nat.find (show
        ∃ index, (Encodable.decode (α := γ) index).elim False p from by
          obtain ⟨witness, validWitness⟩ := h
          exact ⟨Encodable.encode witness, by simp [validWitness]⟩))) = some value := by
      convert equation using 2
      congr 1
      funext index
      cases Encodable.decode (α := γ) index <;> rfl
    rw [decodedValue]
    rfl

noncomputable def search {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : β := Encodable.choose (h a)

omit [Primcodable α] in
lemma search_spec {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : p a (search h a) :=
  Encodable.choose_spec (h a)

lemma computable_search {p : α → β → Prop} [DecidableRel p]
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2))
    (h : ∀a,∃b,p a b) (d : β) : Computable (search h) := by
  have hn : ∀a,∃n,decodeGood (Encodable.decode (α:=β)) p a n := by
    intro a
    obtain ⟨b,hb⟩:=h a
    exact ⟨Encodable.encode b,by simp [decodeGood,hb]⟩
  have hc : Computable (fun a=>Nat.find (hn a)) :=
    Computable.find (computable_decodeGood Computable.decode hp) hn
  exact (Computable.option_getD (Computable.decode.comp hc) (ca_const d)).of_eq (by
    intro a
    convert (choose_getD (h a) d).symm using 3
    all_goals congr 1)
noncomputable def searchWith (e : Encodable β) {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : β := @Encodable.choose β (p a) e _ (h a)

lemma computable_searchWith (e : Encodable β) {p : α → β → Prop} [DecidableRel p]
    (hd : Computable (@Encodable.decode β e))
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2))
    (h : ∀a,∃b,p a b) (d : β) : Computable (searchWith e h) := by
  have hn : ∀a,∃n,decodeGood (@Encodable.decode β e) p a n := by
    intro a
    obtain ⟨b,hb⟩:=h a
    refine ⟨@Encodable.encode β e b,?_⟩
    simp only [decodeGood,Encodable.encodek,Option.elim_some,hb]
  have hc : Computable (fun a=>Nat.find (hn a)) :=
    Computable.find (computable_decodeGood hd hp) hn
  exact (Computable.option_getD (hd.comp hc) (ca_const d)).of_eq (by
    intro a
    convert (@choose_getD β e (p a) _ (h a) d).symm using 3
    all_goals congr 1)
end MinUncut.Preprocess

end

end OAI
