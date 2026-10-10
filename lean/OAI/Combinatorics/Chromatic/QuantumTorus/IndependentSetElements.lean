import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuantumTorusTrace

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

def IsIndependent (u : V → M) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, Ω (u x) (u y)=0

def setMonomial (u : V → M) (s : Finset V) : Torus v Ω :=
  Torus.X v Ω (∑ x ∈ s,u x)

def independentTerm [DecidableEq V] (u : V → M) (k : ℕ) (s : Finset V) : Torus v Ω :=
  if IsIndependent Ω u s ∧ s.card=k then setMonomial v Ω u s else 0

def independentElement [Fintype V] [DecidableEq V] (u : V → M) (k : ℕ) : Torus v Ω :=
  ∑ s : Finset V, independentTerm v Ω u k s

lemma independent_sum_iff (hΩ : ∀m,Ω m m=0) (u : V → M) (w : W → M)
    (s : Finset V) (t : Finset W) :
    IsIndependent Ω (Sum.elim u w) (s.disjSum t) ↔
      IsIndependent Ω u s ∧ IsIndependent Ω w t ∧
        ∀x∈s,∀y∈t,Ω (u x) (w y)=0 := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro x hx y hy
      exact h (.inl x) (by simpa) (.inl y) (by simpa)
    · intro x hx y hy
      exact h (.inr x) (by simpa) (.inr y) (by simpa)
    · intro x hx y hy
      exact h (.inl x) (by simpa) (.inr y) (by simpa)
  · rintro ⟨hs,ht,hst⟩ x hx y hy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hs x (by simpa using hx) y (by simpa using hy)
      | inr y => exact hst x (by simpa using hx) y (by simpa using hy)
    | inr x =>
      cases y with
      | inl y =>
        have H:=alternating_skew Ω hΩ (w x) (u y)
        rw [hst y (by simpa using hy) x (by simpa using hx)] at H
        simpa using H
      | inr y => exact ht x (by simpa using hx) y (by simpa using hy)

lemma sum_labels_disjSum (u : V → M) (w : W → M) (s : Finset V) (t : Finset W) :
    (∑ x ∈ s.disjSum t,Sum.elim u w x)=(∑x∈s,u x)+(∑y∈t,w y) := by
  simp

lemma independent_sum_decomposition [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (u : V → M) (w : W → M) (k : ℕ) :
    independentElement v Ω (Sum.elim u w) k =
      ∑ t : Finset W,∑ s : Finset V, independentTerm v Ω (Sum.elim u w) k (s.disjSum t) := by
  unfold independentElement
  rw [←Equiv.sum_comp (Finset.sumEquiv : Finset (V⊕W) ≃o Finset V×Finset W).symm.toEquiv]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

abbrev Compatible (a : M) (w : W → M) (t : Finset W) : Prop :=
  ∀ y∈t,Ω a (w y)=0

lemma compatible_add (a b : M) (w : W → M) (t : Finset W)
    (hb : Compatible Ω b w t) : Compatible Ω (a+b) w t ↔ Compatible Ω a w t := by
  unfold Compatible at *
  simp only [map_add,AddMonoidHom.add_apply]
  constructor <;> intro h y hy
  · have H:=h y hy
    simpa only [hb y hy,add_zero] using H
  · simpa only [hb y hy,add_zero] using h y hy

lemma finset_fin_three : (Finset.univ : Finset (Finset (Fin 3))) =
    {∅,{0},{1},{2},{0,1},{0,2},{1,2},{0,1,2}} := by decide

lemma independent_triple_sum [DecidableEq W]
    (hΩ : ∀m,Ω m m=0) (a b c : M)
    (hab : Ω a b≠0) (hbc : Ω b c≠0) (hac : Ω a c=0)
    (w : W → M) (t : Finset W) (k : ℕ) :
    (∑ s : Finset (Fin 3),
      independentTerm v Ω (Sum.elim ![a,b,c] w) k (s.disjSum t)) =
    if IsIndependent Ω w t then
      (if t.card=k then Torus.X v Ω (∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω a w t then Torus.X v Ω (a+∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω b w t then Torus.X v Ω (b+∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+∑y∈t,w y) else 0) +
      (if t.card+2=k ∧ Compatible Ω a w t ∧ Compatible Ω c w t then
        Torus.X v Ω (a+c+∑y∈t,w y) else 0)
    else 0 := by
  have hca : Ω c a=0 := by rw [alternating_skew Ω hΩ c a,hac,neg_zero]
  rw [finset_fin_three]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton]
  simp only [independentTerm,independent_sum_iff Ω hΩ,Finset.card_disjSum,
    setMonomial,sum_labels_disjSum]
  by_cases H : IsIndependent Ω w t
  all_goals
    simp only [IsIndependent] at H
    simp [IsIndependent,Compatible,hΩ,hab,hbc,hac,hca,H,
      and_assoc,and_comm,Nat.add_comm,add_assoc]
  simp only [iff_true_intro H,and_true,ite_true]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
