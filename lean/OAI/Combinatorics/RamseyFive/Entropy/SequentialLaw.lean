import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventMass

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def adaptiveLaw (p : Law α) (next : α→Law β) : Law (α×β) where
  mass ab := p ab.1*next ab.1 ab.2
  nonneg ab := mul_nonneg (p.nonneg _) ((next _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,←Finset.mul_sum,(next _).sum_one,mul_one]
    exact p.sum_one

lemma adaptiveLaw_first (p : Law α) (next : α→Law β) :
    first (adaptiveLaw p next)=p := by
  apply Law.ext
  funext a
  change (∑b,p a*next a b)=p a
  rw [←Finset.mul_sum,(next a).sum_one,mul_one]

lemma map_positive (p : Law α) (f : α→β) (b : β) (hb : 0 < map p f b) :
    ∃a,0<p a ∧ f a=b := by
  change 0<(∑a,if f a=b then p a else 0) at hb
  have hn (a : α) (_ : a∈Finset.univ) : 0 ≤ (if f a=b then p a else 0) := by
    split_ifs
    · exact p.nonneg a
    · rfl
  obtain ⟨a,_,ha⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hb
  by_cases he : f a=b
  · exact ⟨a,by simpa [he] using ha,he⟩
  · simp [he] at ha

noncomputable def pureLaw (a : α) : Law α where
  mass b := if b=a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  sum_one := by simp

theorem adaptive_option_failure (p : Law (Option α))
    (next : Option α→Law (Option β)) (ε₁ ε₂ : ℝ) (hε₂ : 0≤ε₂)
    (hfirst : p none≤ε₁) (hnext : ∀a,0 < p (some a) → next (some a) none≤ε₂) :
    eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none) ≤ ε₁+ε₂ := by
  have hinner (a : Option α) (ha : 0 < p a) :
      (∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
        (if a=none then 1 else 0)+ε₂ := by
    cases a with
    | none => simpa only [true_or,ite_true] using
        (show (∑b,next none b)≤1+ε₂ by rw [(next none).sum_one];linarith)
    | some a => simpa using hnext a ha
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a (_ : a∈Finset.univ)=>
    show p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
      p a*((if a=none then 1 else 0)+ε₂) from by
      by_cases hz : p a=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hinner a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a))
  have hl : eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none)=
      ∑a : Option α,p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) := by
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
      Finset.mul_sum,mul_ite,mul_zero]
  rw [hl]
  calc
    _ ≤ ∑a : Option α,p a*((if a=none then 1 else 0)+ε₂) := hsum
    _ = p none+ε₂ := by
      simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
      rw [←Finset.sum_mul,p.sum_one,one_mul]
      simp
    _ ≤ ε₁+ε₂ := by linarith

end

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

noncomputable def finiteImageLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) : Law α where
  mass a := μ.real {ω | f ω=a}
  nonneg a := measureReal_nonneg
  sum_one := by
    have hd : Pairwise (fun a b : α=>Disjoint {ω | f ω=a} {ω | f ω=b}) := by
      intro a b hab
      apply Set.disjoint_left.mpr
      intro ω ha hb
      exact hab (ha.symm.trans hb)
    have he : (⋃a : α,{ω | f ω=a})=Set.univ := by ext ω;simp
    have hh := measureReal_iUnion_fintype (μ:=μ) hd
      (fun a=>Set.Countable.measurableSet (Set.to_countable _))
    rw [he,probReal_univ] at hh
    exact hh.symm

lemma finiteImageLaw_positive (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α)
    (a : α) (ha : 0<finiteImageLaw μ f a) : ∃ω,f ω=a := by
  have hh : μ.real {ω | f ω=a}≠0 := ne_of_gt ha
  exact nonempty_of_measureReal_ne_zero hh

lemma finiteImageLaw_event (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (E : Finset α) :
    eventMass (finiteImageLaw μ f) E=μ.real {ω | f ω∈E} := by
  have hd : Set.PairwiseDisjoint (E:Set α) (fun a=>{ω | f ω=a}) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have he : (⋃a∈E,{ω | f ω=a})={ω | f ω∈E} := by ext ω;simp
  have hh := measureReal_biUnion_finset (μ:=μ) hd
    (fun _ _=>Set.Countable.measurableSet (Set.to_countable _))
  rw [he] at hh
  exact hh.symm

noncomputable def chooseMessage (P : Ω→α→Prop) (ω : Ω) : Option α :=
  if h : ∃a,P ω a then some h.choose else none

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_none (P : Ω→α→Prop) (ω : Ω) :
    chooseMessage P ω=none ↔ ¬∃a,P ω a := by
  unfold chooseMessage
  split <;> simp_all

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_sound (P : Ω→α→Prop) (ω : Ω) (a : α)
    (h : chooseMessage P ω=some a) : P ω a := by
  unfold chooseMessage at h
  split at h
  next hh => exact (Option.some.inj h) ▸ hh.choose_spec
  next hh => contradiction

theorem selectedMessage_failure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω→α→Prop) (E : Set Ω) (ε : ℝ)
    (hE : μ.real Eᶜ≤ε) (hs : ∀ω∈E,∃a,P ω a) :
    finiteImageLaw μ (chooseMessage P) none≤ε := by
  apply (measureReal_mono (μ:=μ) (show {ω | chooseMessage P ω=none}⊆Eᶜ from ?_)).trans hE
  intro ω hω he
  exact (chooseMessage_none P ω).mp hω (hs ω he)

end SharpRamseyFive.FiniteEntropy

end OAI
