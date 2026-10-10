import Mathlib
import OAI.GroupTheory.SimpleOvergroups.NamedActions

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations
variable {G X : Type*} [Primcodable G] [Primcodable X] (N : Operations G X)
attribute [local fun_prop] Primrec
attribute [local fun_prop] Primrec.id Primrec.const Primrec.fst Primrec.snd Primrec.pair Primrec.comp
attribute [local fun_prop] Primrec.option_some Primrec.sumInl Primrec.sumInr
private theorem primrec_cons {A : Type*} [Primcodable A] :
    Primrec (fun p : A × List A => p.1 :: p.2) := Primrec.list_cons
private theorem primrec_append {A : Type*} [Primcodable A] :
    Primrec (fun p : List A × List A => p.1 ++ p.2) := Primrec.list_append
attribute [local fun_prop] primrec_cons primrec_append

private theorem primrec_match_list {A B R : Type*} [Primcodable A] [Primcodable B] [Primcodable R]
    {f : A → List B} {g : A → R} {h : A → B × List B → R}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | [] => g a | b::l => h a (b,l)) :=
  (Primrec.list_casesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)
private theorem primrec_match_option {A B R : Type*} [Primcodable A] [Primcodable B] [Primcodable R]
    {f : A → Option B} {g : A → R} {h : A → B → R}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | none => g a | some b => h a b) :=
  (Primrec.option_casesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)
private theorem primrec_match_sum {A B C R : Type*}
    [Primcodable A] [Primcodable B] [Primcodable C] [Primcodable R]
    {f : A → B ⊕ C} {g : A → B → R} {h : A → C → R}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | .inl b => g a b | .inr c => h a c) :=
  (Primrec.sumCasesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)

 theorem primrec_letterCost (hg : Primrec N.gcost) (hx : Primrec N.xcost) :
    Primrec N.letterCost := by
  have ho : Primrec (fun p : Letter G X × Option X =>
      match p.2 with | none => 0 | some x => N.xcost x) :=
    primrec_match_option Primrec.snd (Primrec.const 0) (hx.comp Primrec.snd).to₂
  have hs : Primrec (fun p : Letter G X × (X ⊕ Option X) =>
      match p.2 with
      | .inl x => N.xcost x
      | .inr o => match o with | none => 0 | some x => N.xcost x) :=
    (primrec_match_sum Primrec.snd (hx.comp Primrec.snd).to₂
      (ho.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
        (fun p => by cases p.2 <;> rfl)
  exact (primrec_match_sum Primrec.id (hg.comp Primrec.snd).to₂ hs.to₂).of_eq
    (fun a => by rcases a with g | (x | y); rfl; rfl; cases y <;> rfl)

 theorem primrec_plan (hm : Primrec₂ N.mul) (hi : Primrec N.inv) (ha : Primrec₂ N.act) :
    Primrec₂ N.plan := by
  have hm' : Primrec (fun p : G × G => N.mul p.1 p.2) := hm
  have ha' : Primrec (fun p : G × X => N.act p.1 p.2) := ha
  let T := Letter G X × Form G X
  let B := List X × G × List X
  let R := Form G X ⊕ (X × X × Form G X)
  have hgrp : Primrec (fun p : (T × B) × G =>
      match p.1.2.1 with
      | [] => (Sum.inl (some ([],N.mul p.2 p.1.2.2.1,p.1.2.2.2)) : Form G X ⊕ (X × X × Form G X))
      | x::l => .inl (some (N.act p.2 x::l,p.1.2.2.1,p.1.2.2.2))) := by
    have h0 : Primrec (fun p : (T × B) × G => (Sum.inl
        (some ([],N.mul p.2 p.1.2.2.1,p.1.2.2.2)) : R)) := by
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    have hc : Primrec₂ (fun (p : (T × B) × G) (q : X × List X) =>
        (Sum.inl (some (N.act p.2 q.1::q.2,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    exact (primrec_match_list (f := fun p : (T × B) × G => p.1.2.1)
      (by dsimp only [B,T,R]; fun_prop) h0 hc).of_eq (fun p => by cases p.1.2.1 <;> rfl)
  have hdel : Primrec (fun p : (T × B) × X =>
      match p.1.2.1 with
      | [] => (Sum.inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) p.2])) :
          Form G X ⊕ (X × X × Form G X))
      | x::l => .inr (p.2,x,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    have h0 : Primrec (fun p : (T × B) × X => (Sum.inl
        (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) p.2])) : R)) := by
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    have hc : Primrec₂ (fun (p : (T × B) × X) (q : X × List X) =>
        (Sum.inr (p.2,q.1,some (q.2,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop
    exact (primrec_match_list (f := fun p : (T × B) × X => p.1.2.1)
      (by dsimp only [B,T,R]; fun_prop) h0 hc).of_eq (fun p => by cases p.1.2.1 <;> rfl)
  have hopt : Primrec (fun p : (T × B) × Option X =>
      match p.2 with
      | none => (Sum.inl none : Form G X ⊕ (X × X × Form G X))
      | some x => match p.1.2.1 with
        | [] => .inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) x]))
        | z::l => .inr (x,z,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    apply primrec_match_option Primrec.snd (Primrec.const (Sum.inl none))
    exact (hdel.comp (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)).to₂
  have hnon : Primrec (fun p : (T × B) × (X ⊕ Option X) =>
      match p.2 with
      | .inl x => (Sum.inl (some (x::p.1.2.1,p.1.2.2.1,p.1.2.2.2)) :
          Form G X ⊕ (X × X × Form G X))
      | .inr y => match y with
        | none => .inl none
        | some x => match p.1.2.1 with
          | [] => .inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) x]))
          | z::l => .inr (x,z,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    have hl : Primrec₂ (fun (p : (T × B) × (X ⊕ Option X)) (x : X) =>
        (Sum.inl (some (x::p.1.2.1,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop
    exact (primrec_match_sum Primrec.snd hl
      (hopt.comp (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)).to₂).of_eq
        (fun p => by cases p.2 <;> rfl)
  have hs : Primrec (fun p : T × B => N.plan p.1.1 (some p.2)) := by
    apply (Primrec.sumCasesOn (Primrec.fst.comp Primrec.fst)
      (hgrp.to₂) (hnon.to₂)).of_eq
    intro p
    rcases p with ⟨⟨a,f⟩,l,g,r⟩
    rcases a with h | (x|y)
    · cases l <;> rfl
    · rfl
    · cases y with
      | none => rfl
      | some y => cases l <;> rfl
  exact (Primrec.option_casesOn Primrec.snd (Primrec.const (.inl none)) hs.to₂).of_eq
    (fun p => by rcases p with ⟨a,f⟩; cases f <;> rfl)
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations

end OAI
