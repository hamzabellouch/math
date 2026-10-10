import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Computable
attribute [fun_prop] Primrec.to_comp

def CompPred {A : Type} [Primcodable A] (p : A → Prop) [DecidablePred p] : Prop :=
  Computable (fun a => decide (p a))
attribute [fun_prop] CompPred

@[fun_prop] lemma compPred_primrec {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : PrimrecPred p) : CompPred p := hp.decide.to_comp

@[fun_prop] lemma compPred_comp {A B : Type} [Primcodable A] [Primcodable B]
    {p : B → Prop} [DecidablePred p] {f : A → B}
    (hp : CompPred p) (hf : Computable f) : CompPred (fun a => p (f a)) := hp.comp hf

@[fun_prop] lemma compPred_and {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (hq : CompPred q) :
    CompPred (fun a => p a ∧ q a) := by
  exact (Primrec.and.to_comp.comp hp hq).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_or {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (hq : CompPred q) :
    CompPred (fun a => p a ∨ q a) := by
  exact (Primrec.or.to_comp.comp hp hq).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_not {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : CompPred p) : CompPred (fun a => ¬p a) := by
  exact (Primrec.not.to_comp.comp hp).of_eq (fun a => by simp)

@[fun_prop] lemma computable_ite {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} [DecidablePred p] {f g : A → B}
    (hp : CompPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  exact (Computable.cond hp hf hg).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_decide {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : CompPred p) : Computable (fun a => decide (p a)) := hp

lemma CompPred.of_eq {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (h : ∀ a, p a ↔ q a) : CompPred q :=
  Computable.of_eq hp (fun a => by simp [h a])

lemma computable_of_compGraph {A B : Type} [Primcodable A] [Primcodable B]
    (f : A → B) (R : A → B → Prop) [DecidableRel R]
    (hR : CompPred (fun p : A × B => R p.1 p.2))
    (h : ∀ a b, R a b ↔ b = f a) : Computable f := by
  let test : A → ℕ → Option B := fun a n =>
    (decode n).bind fun b => if R a b then some b else none
  have ht : Computable₂ test :=
    Computable.option_bind (Computable.decode.comp Computable.snd)
      (computable_ite (compPred_comp hR ((Computable.fst.comp Computable.fst).pair Computable.snd))
        (Computable.option_some.comp Computable.snd) (Computable.const none)).to₂
  apply (Partrec.rfindOpt ht).of_eq_tot
  intro a
  have hd : (Nat.rfindOpt (test a)).Dom := Nat.rfindOpt_dom.mpr
    ⟨encode (f a), f a, by simp [test, Encodable.encodek, (h a (f a)).mpr rfl]⟩
  have hm : (Nat.rfindOpt (test a)).get hd ∈ Nat.rfindOpt (test a) := ⟨hd, rfl⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hm
  have he : (Nat.rfindOpt (test a)).get hd = f a := by
    simp only [test, Option.mem_bind_iff] at hn
    obtain ⟨b, _, hb⟩ := hn
    split_ifs at hb with hab
    · obtain rfl := Option.mem_some_iff.mp hb
      exact (h a _).mp hab
    · contradiction
  exact he ▸ hm

end RapidForcing.EffectiveArithmetic

end

end OAI
