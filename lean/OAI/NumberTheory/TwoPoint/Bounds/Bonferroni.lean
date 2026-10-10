import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-! The finite even-order sieve, before any independence or prime estimates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def avoidsEvents {ι α : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) : Prop :=
  ∀ i ∈ P, ¬E i x

def eventIntersection {ι α : Type*} (E : ι → α → Prop) (S : Finset ι) (x : α) : Prop :=
  ∀ i ∈ S, E i x

noncomputable def eventIntersectionCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) : ℝ :=
  ∑ S ∈ P.powersetCard j, if eventIntersection E S x then 1 else 0

noncomputable def truncatedEventCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionCount P E j x

lemma eventIntersectionCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) :
    eventIntersectionCount P E j x = ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  have hfilter : (P.powersetCard j).filter (fun S => eventIntersection E S x) =
      (P.filter (fun i => E i x)).powersetCard j := by
    apply Finset.ext
    intro S
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    simp only [eventIntersection]
    constructor
    · rintro ⟨⟨hS, hcard⟩, hE⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hS hi, hE i hi⟩, hcard⟩
    · rintro ⟨hS, hcard⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hS hi)).1, hcard⟩,
        fun i hi => (mem_filter.mp (hS hi)).2⟩
  unfold eventIntersectionCount
  rw [← sum_filter, hfilter]
  simp

lemma truncatedEventCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E r x =
      ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j *
        ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  simp only [truncatedEventCount, eventIntersectionCount_eq_choose]

lemma avoidsEvents_iff_card_zero {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (x : α) :
    avoidsEvents P E x ↔ (P.filter (fun i => E i x)).card = 0 := by
  simp only [avoidsEvents, card_eq_zero, filter_eq_empty_iff]

lemma real_alternating_choose (n r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ)) =
      (-1 : ℝ) ^ r * (n.choose r : ℝ) := by
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := r))

lemma alternating_choose_zero (r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp
  · intro h
    exact False.elim (h (mem_range.mpr (Nat.zero_lt_succ r)))

lemma even_binomial_lower (k r : ℕ) :
    (if k = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ range (2 * r + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) := by
  cases k with
  | zero => simp only [ite_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r)]
      have he : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
      simp only [Nat.succ_ne_zero, ite_false, he, one_mul]
      positivity

lemma odd_binomial_upper (k r : ℕ) :
    (∑ j ∈ range ((2 * r + 1) + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ)) ≤
      if k = 0 then (1 : ℝ) else 0 := by
  cases k with
  | zero => simp only [ite_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r + 1)]
      have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      simp only [Nat.succ_ne_zero, ite_false, he, neg_one_mul]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

/-- Even truncation dominates the actual avoidance indicator pointwise. -/
theorem bonferroni_even_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    (if avoidsEvents P E x then (1 : ℝ) else 0) ≤ truncatedEventCount P E (2 * r) x := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using even_binomial_lower (P.filter (fun i => E i x)).card r

/-- Odd truncation gives the opposite bound. -/
theorem bonferroni_odd_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x ≤
      if avoidsEvents P E x then (1 : ℝ) else 0 := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using odd_binomial_upper (P.filter (fun i => E i x)).card r

lemma truncatedEventCount_odd {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x =
      truncatedEventCount P E (2 * r) x - eventIntersectionCount P E (2 * r + 1) x := by
  unfold truncatedEventCount
  rw [sum_range_succ]
  have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [he]
  ring

/-- The excess of the even truncation is bounded by the very next
intersection layer. No convergence argument is involved. -/
theorem bonferroni_remainder_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r) x ≤
      (if avoidsEvents P E x then (1 : ℝ) else 0) +
        eventIntersectionCount P E (2 * r + 1) x := by
  have hh := bonferroni_odd_pointwise P E r x
  rw [truncatedEventCount_odd] at hh
  linarith

noncomputable def eventIntersectionMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, μ.probability (eventIntersection E S)

noncomputable def truncatedEventMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionMass μ P E j

lemma average_eventIntersectionCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) :
    μ.average (eventIntersectionCount P E j) = eventIntersectionMass μ P E j := by
  unfold eventIntersectionCount eventIntersectionMass FiniteLaw.probability FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]

lemma average_truncatedEventCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.average (truncatedEventCount P E r) = truncatedEventMass μ P E r := by
  unfold truncatedEventCount truncatedEventMass FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  calc
    _ = (-1 : ℝ) ^ j * μ.average (eventIntersectionCount P E j) := by
      unfold FiniteLaw.average
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [average_eventIntersectionCount]

theorem bonferroni_even {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.probability (avoidsEvents P E) ≤ truncatedEventMass μ P E (2 * r) := by
  rw [← average_truncatedEventCount]
  exact μ.average_mono (bonferroni_even_pointwise P E r)

theorem bonferroni_remainder {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    truncatedEventMass μ P E (2 * r) ≤ μ.probability (avoidsEvents P E) +
      eventIntersectionMass μ P E (2 * r + 1) := by
  rw [← average_truncatedEventCount, ← average_eventIntersectionCount]
  have hh := μ.average_mono (bonferroni_remainder_pointwise P E r)
  simpa only [FiniteLaw.probability, FiniteLaw.average, mul_add, sum_add_distrib] using hh

/-- Total error in the finitely many intersection counts used by a sieve
truncation. Each subset appears just once. -/
noncomputable def sieveIntersectionError {ι : Type*}
    (P : Finset ι) (err : Finset ι → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j, err S

lemma truncatedEventMass_comparison {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    truncatedEventMass μ P E r ≤ truncatedEventMass ν P F r +
      sieveIntersectionError P err r := by
  have heq : truncatedEventMass μ P E r - truncatedEventMass ν P F r =
      ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j,
        (-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)) := by
    simp only [truncatedEventMass, eventIntersectionMass, mul_sum,
      mul_sub, sum_sub_distrib]
  have hb : truncatedEventMass μ P E r - truncatedEventMass ν P F r ≤
      sieveIntersectionError P err r := by
    rw [heq]
    apply sum_le_sum
    intro j hj
    apply sum_le_sum
    intro S hS
    obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
    calc
      _ ≤ |(-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S))| := le_abs_self _
      _ = |μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)| := by
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ err S := herr S (mem_powerset.mpr hSP)
        (by rw [hcard]; exact Nat.le_of_lt_succ (mem_range.mp hj))
  linarith

/-- Exact finite sieve transfer. An independent residue model can be
inserted only after its intersections have actually been counted. -/
theorem bonferroni_transfer {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ 2 * r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    μ.probability (avoidsEvents P E) ≤ ν.probability (avoidsEvents P F) +
      eventIntersectionMass ν P F (2 * r + 1) + sieveIntersectionError P err (2 * r) := by
  have h₁ := bonferroni_even μ P E r
  have h₂ := truncatedEventMass_comparison μ ν P E F (2 * r) err herr
  have h₃ := bonferroni_remainder ν P F r
  linarith

end TwoPointCorrelations

end OAI
