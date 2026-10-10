import Mathlib
import OAI.Computability.MinUncut.PCP.Occurrences

namespace OAI

section
namespace MinUncut
open MinUncutGames.Foundations.Hastad.SourceOccurrences

structure Enumeration (A : Type) where
  values : List A
  nodup : values.Nodup
  complete : ∀ a, a∈values

namespace Enumeration
variable {A B : Type}

def ofList [DecidableEq A] (l : List A) (h : ∀a, a∈l) : Enumeration A where
  values := l.dedup
  nodup := List.nodup_dedup l
  complete a := List.mem_dedup.mpr (h a)

def encoding [DecidableEq A] (E : Enumeration A) : Encoding A where
  size := E.values.length
  code := (List.Nodup.getEquivOfForallMemList E.values E.nodup E.complete).symm

def ofEncoding (e : Encoding A) : Enumeration A where
  values := e.enumerate
  nodup := e.nodup_enumerate
  complete := e.mem_enumerate

def image [DecidableEq B] (E : Enumeration A) (f : A → B) (h : Function.Surjective f) : Enumeration B :=
  ofList (E.values.map f) (by intro b; obtain ⟨a,rfl⟩ := h b; exact List.mem_map.mpr ⟨a,E.complete a,rfl⟩)

def subtype [DecidableEq A] (E : Enumeration A) (p : A → Prop) [DecidablePred p] : Enumeration {a // p a} :=
  ofList ((E.values.filter (fun a => decide (p a))).attach.map (fun a =>
    (⟨a.val, by
      have hm : a.val ∈ E.values ∧ decide (p a.val) = true := List.mem_filter.mp a.property
      exact of_decide_eq_true hm.2⟩ : {a // p a}))) (by
    intro a
    apply List.mem_map.mpr
    exact ⟨⟨a.val,List.mem_filter.mpr ⟨E.complete a.val,by simpa only [decide_eq_true_eq] using a.property⟩⟩,List.mem_attach _ _,rfl⟩)

def sigma [DecidableEq A] (E : Enumeration A) {B : A → Type} [∀a, DecidableEq (B a)]
    (F : ∀a, Enumeration (B a)) : Enumeration (Σa, B a) :=
  ofList (E.values.flatMap (fun a => (F a).values.map (fun b => Sigma.mk a b))) (by
    rintro ⟨a,b⟩
    exact List.mem_flatMap.mpr ⟨a,E.complete a,List.mem_map.mpr ⟨b,(F a).complete b,rfl⟩⟩)

def pair [DecidableEq A] [DecidableEq B] (E : Enumeration A) (F : Enumeration B) : Enumeration (A × B) :=
  ofEncoding (E.encoding.prod F.encoding)

def function [DecidableEq A] [DecidableEq B] (E : Enumeration A) (F : Enumeration B) : Enumeration (A → B) :=
  ofEncoding (E.encoding.function F.encoding)

lemma length_values [Fintype A] (E : Enumeration A) : E.values.length=Fintype.card A := by
  classical
  have he : E.values.toFinset=Finset.univ := by ext a; simp [E.complete]
  rw [← List.toFinset_card_of_nodup E.nodup,he,Finset.card_univ]

lemma prod_values {M : Type*} [CommMonoid M] [Fintype A] (E : Enumeration A) (f : A → M) :
    (E.values.map f).prod=∏a, f a := by
  classical
  have he : E.values.toFinset=Finset.univ := by ext a; simp [E.complete]
  rw [← List.prod_toFinset f E.nodup,he]

lemma sum_values [Fintype A] (E : Enumeration A) (f : A → ℕ) :
    (E.values.map f).sum=∑a, f a := by
  classical
  have he : E.values.toFinset=Finset.univ := by ext a; simp [E.complete]
  rw [← List.sum_toFinset f E.nodup]
  rw [he]
end Enumeration
end MinUncut

end

end OAI
