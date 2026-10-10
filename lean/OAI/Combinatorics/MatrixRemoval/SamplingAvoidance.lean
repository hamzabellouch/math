import Mathlib

namespace OAI


/-!
# Avoiding a finite family of events by counting

The cardinality of a finite union is bounded by the sum of the individual
cardinalities. A strict bound below the size of the ambient finite type
therefore supplies an element outside every event. The rational corollary
uses normalized cardinalities and requires no independence assumption.
-/

universe uOmega uI uCell uValue

namespace Problem348.Sampling

open scoped BigOperators

/-- A family of finite bad events whose summed cardinality is smaller than the
ambient finite type has an element avoiding every event in the family. -/
theorem exists_avoiding_of_sum_card_lt {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω)
    (hsmall : (∑ i ∈ events, (bad i).card) < Fintype.card Ω) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  classical
  have hUnion : (events.biUnion bad).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt Finset.card_biUnion_le hsmall
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hUnion
  refine ⟨ω, ?_⟩
  intro i hi hbad
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)

/-- Uniform rational bounds on the normalized bad-event cardinalities give an
avoiding element when the number of events times the bound is less than one.
The events may overlap arbitrarily. -/
theorem exists_avoiding_of_uniform_ratio_lt {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (r : ℚ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, ((bad i).card : ℚ) / (Fintype.card Ω : ℚ) ≤ r)
    (hsmall : (events.card : ℚ) * r < 1) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hpos : (0 : ℚ) < (Fintype.card Ω : ℚ) := Nat.cast_pos.mpr hΩ
  have hsum : (∑ i ∈ events, ((bad i).card : ℚ)) < (Fintype.card Ω : ℚ) := by
    calc
      (∑ i ∈ events, ((bad i).card : ℚ))
          ≤ ∑ i ∈ events, r * (Fintype.card Ω : ℚ) :=
        Finset.sum_le_sum fun i hi => (div_le_iff₀ hpos).mp (hbound i hi)
      _ = (events.card : ℚ) * r * (Fintype.card Ω : ℚ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ < 1 * (Fintype.card Ω : ℚ) := mul_lt_mul_of_pos_right hsmall hpos
      _ = (Fintype.card Ω : ℚ) := one_mul _
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.cast_lt (α := ℚ)).mp
  simpa only [Nat.cast_sum] using hsum

/-- A fraction-free uniform union bound.  Every bad event occupies at most
`1 / q` of the finite sample space; fewer than `q` bad events can be avoided.
No independence between the bad events is required. -/
theorem exists_avoiding_of_card_mul_le {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (q : ℕ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, (bad i).card * q ≤ Fintype.card Ω)
    (hsmall : events.card < q) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hsmall
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.mul_lt_mul_right hq).mp
  calc
    (∑ i ∈ events, (bad i).card) * q
        = ∑ i ∈ events, (bad i).card * q := Finset.sum_mul _ _ _
    _ ≤ ∑ _i ∈ events, Fintype.card Ω := Finset.sum_le_sum hbound
    _ = events.card * Fintype.card Ω := by simp
    _ < q * Fintype.card Ω := Nat.mul_lt_mul_of_pos_right hsmall hΩ
    _ = Fintype.card Ω * q := Nat.mul_comm _ _

/-- The cellwise counting form of sampling avoidance.
The relation `selected ω e` means that sample `ω` uses the relevant cell `e`.
The budget is the square of the common size of the axis classes. -/
theorem exists_selection_avoiding {Ω : Type uOmega} {Cell : Type uCell} [Fintype Ω]
    (changed : Finset Cell) (selected : Ω → Cell → Prop) (m : ℕ)
    [DecidableRel selected]
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e ∈ changed,
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hsmall : changed.card < m ^ 2) :
    ∃ ω, ∀ e ∈ changed, ¬ selected ω e := by
  obtain ⟨ω, hω⟩ := exists_avoiding_of_card_mul_le changed
    (fun e => Finset.univ.filter (fun ω => selected ω e)) (m ^ 2) hΩ hbound hsmall
  exact ⟨ω, fun e he hs => hω e he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩

/-- Agreement on every protected selected cell follows from the cellwise
sampling estimate.  Unprotected cells are allowed to change arbitrarily. -/
theorem exists_agreement_of_changed_card_lt
    {Ω : Type uOmega} {Cell : Type uCell} {Value : Type uValue} [Fintype Ω] [Fintype Cell] [DecidableEq Value]
    (A B : Cell → Value) (selected : Ω → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (m : ℕ) (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hsmall : (Finset.univ.filter (fun e => A e ≠ B e)).card < m ^ 2) :
    ∃ ω, ∀ e, relevant e → selected ω e → A e = B e := by
  classical
  let changed := Finset.univ.filter (fun e => A e ≠ B e)
  let events := changed.filter relevant
  have hsmall' : events.card < m ^ 2 :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) hsmall
  obtain ⟨ω, hω⟩ := exists_selection_avoiding events selected m hΩ
    (fun e he => hbound e (Finset.mem_filter.mp he).2) hsmall'
  refine ⟨ω, ?_⟩
  intro e he hs
  by_contra hne
  exact hω e (by simp [events, changed, he, hne]) hs

/-- Version for the three-seed sample space used in the tree construction.
There are `m³` samples, and a protected cell occurs in at most `m` of them. -/
theorem exists_agreement_three_seed
    {Cell : Type uCell} {Value : Type uValue} [Fintype Cell] [DecidableEq Value]
    (m : ℕ) (hm : 0 < m) (A B : Cell → Value)
    (selected : (Fin m × Fin m × Fin m) → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card ≤ m)
    (hsmall : (Finset.univ.filter (fun e => A e ≠ B e)).card < m ^ 2) :
    ∃ ω, ∀ e, relevant e → selected ω e → A e = B e := by
  apply exists_agreement_of_changed_card_lt A B selected relevant m
  · simpa using Nat.mul_pos hm (Nat.mul_pos hm hm)
  · intro e he
    calc
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2
          ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (hbound e he)
      _ = Fintype.card (Fin m × Fin m × Fin m) := by
        simp [pow_two]
  · exact hsmall

/-- Contrapositive form: if every sample forces a changed protected cell,
then at least `m²` entries have changed. -/
theorem sq_le_changed_card_of_forcing
    {Ω : Type uOmega} {Cell : Type uCell} {Value : Type uValue} [Fintype Ω] [Fintype Cell] [DecidableEq Value]
    (A B : Cell → Value) (selected : Ω → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (m : ℕ) (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hforcing : ∀ ω, ∃ e, relevant e ∧ selected ω e ∧ A e ≠ B e) :
    m ^ 2 ≤ (Finset.univ.filter (fun e => A e ≠ B e)).card := by
  by_contra h
  obtain ⟨ω, hω⟩ := exists_agreement_of_changed_card_lt A B selected relevant m
    hΩ hbound (Nat.lt_of_not_ge h)
  obtain ⟨e, he, hs, hne⟩ := hforcing ω
  exact hne (hω e he hs)

end Problem348.Sampling

end OAI
