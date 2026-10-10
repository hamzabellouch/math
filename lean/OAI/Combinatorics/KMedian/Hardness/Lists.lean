import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Projection
import OAI.Combinatorics.KMedian.Hardness.TwoChoices

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def DuplicateConsistent : Prop :=
  ∀ v i j, G.neighbor v i = G.neighbor v j → ∀ a, G.project v i a = G.project v j a

omit [Fintype U] [Fintype V] [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq U] [DecidableEq V] [DecidableEq I] [DecidableEq A] [DecidableEq B] in
theorem consistent_of_injective (hinj : ∀ v, Function.Injective (G.neighbor v)) :
    G.DuplicateConsistent := by
  intro v i j hij a
  rw [hinj v hij]

def agreement (left : U → A) : Finset V :=
  univ.filter (fun v => ∃ i j, i ≠ j ∧
    G.project v i (left (G.neighbor v i)) = G.project v j (left (G.neighbor v j)))

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq A] in
@[simp] theorem mem_agreement (left : U → A) (v : V) :
    v ∈ G.agreement left ↔ ∃ i j, i ≠ j ∧
    G.project v i (left (G.neighbor v i)) = G.project v j (left (G.neighbor v j)) := by
  simp [agreement]

def heavyHit (S : Finset (U × A)) (t : ℕ) : Finset V :=
  univ.filter (fun v => ∃ i, t < (labels S (G.neighbor v i)).card)

def lowBad (S : Finset (U × A)) (t : ℕ) : Finset V := G.bad S \ G.heavyHit S t

omit [Fintype B] [DecidableEq I] [DecidableEq B] in
theorem heavy_bound {d : ℕ} (hreg : G.LeftRegular d)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) (t : ℕ) :
    t * (G.heavyHit S t).card ≤ Fintype.card I * Fintype.card V := by
  have hp (v : V) : (if v ∈ G.heavyHit S t then t else 0) ≤
      ∑ i, (labels S (G.neighbor v i)).card := by
    split_ifs with hv
    · obtain ⟨i,hi⟩ := (show ∃ i, t < (labels S (G.neighbor v i)).card by
        simpa only [heavyHit,mem_filter,mem_univ,true_and] using hv)
      exact hi.le.trans (single_le_sum (f := fun i => (labels S (G.neighbor v i)).card)
        (fun _ _ => Nat.zero_le _) (mem_univ i))
    · exact Nat.zero_le _
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  have he : (∑ v, if v ∈ G.heavyHit S t then t else 0) = t*(G.heavyHit S t).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [he,G.regular_sum hreg (fun u => (labels S u).card),labels_sum] at hh
  exact hh.trans ((Nat.mul_le_mul_left d hS).trans_eq (G.regular_degrees hreg))

def cappedLabels (S : Finset (U × A)) (t : ℕ) (default : A) (u : U) : Finset A :=
  if (labels S u).card ≤ t ∧ (labels S u).Nonempty then labels S u else {default}

omit [Fintype U] in
theorem capped_nonempty (S : Finset (U × A)) (t : ℕ) (default : A) (u : U) :
    (cappedLabels S t default u).Nonempty := by
  unfold cappedLabels
  split_ifs with h
  · exact h.2
  · exact singleton_nonempty _

omit [Fintype U] in
theorem capped_card (S : Finset (U × A)) {t : ℕ} (ht : 1 ≤ t) (default : A) (u : U) :
    (cappedLabels S t default u).card ≤ t := by
  unfold cappedLabels
  split_ifs with h
  · exact h.1
  · simpa only [card_singleton] using ht

omit [Fintype U] in
theorem mem_capped (S : Finset (U × A)) {t : ℕ} (default : A) {u : U} {a : A}
    (hsmall : (labels S u).card ≤ t) (ha : (u,a) ∈ S) :
    a ∈ cappedLabels S t default u := by
  have hm : a ∈ labels S u := (mem_labels S u a).mpr ha
  rw [cappedLabels,ite_eq_left ⟨hsmall,⟨a,hm⟩⟩]
  exact hm

theorem lowBad_bound (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.lowBad S t).card:ℝ) ≤ (t:ℝ)^2*γ*Fintype.card V := by
  classical
  let C (u : U) := {a : A // a ∈ cappedLabels S t default u}
  have hc (u : U) : Fintype.card (C u) ≤ t := by
    simpa only [C,Fintype.card_coe] using capped_card S ht default u
  let (u : U) : Nonempty (C u) :=
    let ⟨a,ha⟩ := capped_nonempty S t default u
    ⟨⟨a,ha⟩⟩
  let events (f : ∀u, C u) := G.agreement (fun u => (f u).val)
  apply two_choice_or_trivial_event_bound C ht hc events (G.lowBad S t) _ γ (fun f => hsound _)
  intro v hv
  have hbad : v ∈ G.bad S := (mem_sdiff.mp hv).1
  have hlow : v ∉ G.heavyHit S t := (mem_sdiff.mp hv).2
  have hsmall : ∀ i, (labels S (G.neighbor v i)).card ≤ t := by
    simpa only [heavyHit,mem_filter,mem_univ,true_and,not_exists,not_lt] using hlow
  obtain ⟨b,hb⟩ := (show ∃ b, 1 < (G.parts S v b).card by
    simpa only [bad,mem_filter,mem_univ,true_and] using hbad)
  obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp hb
  obtain ⟨a,ha,hpa⟩ := (G.mem_parts S v b i).mp hi
  obtain ⟨a',ha',hpa'⟩ := (G.mem_parts S v b j).mp hj
  let aC : C (G.neighbor v i) := ⟨a,mem_capped S default (hsmall i) ha⟩
  let bC : C (G.neighbor v j) := ⟨a',mem_capped S default (hsmall j) ha'⟩
  by_cases hsame : G.neighbor v i = G.neighbor v j
  · left
    intro f
    apply (G.mem_agreement _ v).mpr
    refine ⟨i,j,hij,?_⟩
    rw [hdup v i j hsame,hsame]
  · right
    refine ⟨G.neighbor v i,G.neighbor v j,hsame,aC,bC,?_⟩
    intro f hf hg
    change v ∈ G.agreement (fun u => (f u).val)
    apply (G.mem_agreement _ v).mpr
    refine ⟨i,j,hij,?_⟩
    rw [hf,hg]
    exact hpa.trans hpa'.symm

theorem bad_bound {d : ℕ} (hreg : G.LeftRegular d)
    (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.bad S).card:ℝ) ≤ ((Fintype.card I:ℝ)/t+(t:ℝ)^2*γ)*Fintype.card V := by
  have hl := G.lowBad_bound hdup S ht default γ hsound
  have hh := G.heavy_bound hreg S hS t
  have hr : (t:ℝ)*((G.heavyHit S t).card:ℝ) ≤
      (Fintype.card I:ℝ)*Fintype.card V := by exact_mod_cast hh
  have hc : (G.bad S).card ≤ (G.lowBad S t).card+(G.heavyHit S t).card := by
    have he : G.bad S ⊆ G.lowBad S t ∪ G.heavyHit S t := by
      intro v hv
      by_cases hh : v ∈ G.heavyHit S t
      · exact mem_union_right _ hh
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hh⟩)
    exact (card_le_card he).trans (card_union_le _ _)
  have hcr : ((G.bad S).card:ℝ) ≤ (G.lowBad S t).card+(G.heavyHit S t).card := by
    exact_mod_cast hc
  have ht0 : (0:ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hheavy : ((G.heavyHit S t).card:ℝ) ≤
      (Fintype.card I:ℝ)/t*Fintype.card V := by
    calc
      _ ≤ ((Fintype.card I:ℝ)*Fintype.card V)/t :=
        (le_div_iff₀ ht0).mpr (by nlinarith [hr])
      _ = _ := by ring
  nlinarith

theorem coverage_agreement_bound {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.covered S).card:ℝ) ≤
      (1-(1-1/(Fintype.card I:ℝ))^Fintype.card I+
        (Fintype.card I:ℝ)/t+(t:ℝ)^2*γ) *
        ((Fintype.card V:ℝ)*(Fintype.card I:ℝ)^Fintype.card B) := by
  have hc := G.coverage_bound hreg hI S hS
  have hb := G.bad_bound hreg hdup S hS ht default γ hsound
  have hm := mul_le_mul_of_nonneg_left hb
    (pow_nonneg (Nat.cast_nonneg (Fintype.card I)) (Fintype.card B) :
      (0:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B)
  nlinarith

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
