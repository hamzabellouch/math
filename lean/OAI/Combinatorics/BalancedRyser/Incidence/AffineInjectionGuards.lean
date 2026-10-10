import OAI.Combinatorics.BalancedRyser.Incidence.AffineInjectionExposure

namespace OAI

namespace Balanced.InjectionExposure
open scoped _root_.Balanced

variable {I J Z : Type*} [Fintype I] [Fintype J] [Fintype Z]
  [DecidableEq I] [DecidableEq J]

theorem auxiliary_next_event_probability_le_budget
    (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (hnoise : DependsOnExposed K noise)
    (i : I) (hi : i ∉ K) (P : Z → J → Prop) [∀ z, DecidablePred (P z)]
    (hP : ∀ z, ((remaining K base).filter (P z)).card ≤ 1)
    (N : ℕ) (hK : K.card ≤ N) (hN : N < Fintype.card J) :
    ((auxiliaryLaw K base noise).toOuterMeasure {x | P x.2 (x.1 i)}).toReal ≤
      1 / ((Fintype.card J - N : ℕ) : ℝ) := by
  apply (auxiliary_next_event_probability_le K base noise hnoise i hi P hP).trans
  rw [card_remaining]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.sub_pos_of_lt hN
  · exact_mod_cast Nat.sub_le_sub_left hK (Fintype.card J)

end Balanced.InjectionExposure

namespace Balanced
open scoped _root_.Balanced

variable {F I Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype Z]

theorem auxiliary_guarded_joining_probability_le
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p r : Z → Point F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | p x.2 ≠ r x.2 ∧ OnLine (r x.2) (lineThrough (x.1 i) (p x.2))}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.auxiliary_next_event_probability_le K base noise hnoise i hi
    (fun z d => p z ≠ r z ∧ OnLine (r z) (lineThrough d (p z))) (by
      intro z
      apply Finset.card_le_one.mpr
      intro d hd e he
      obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hd
      obtain ⟨_, _, he⟩ := Finset.mem_filter.mp he
      exact direction_eq_of_common_point (p z) (r z) hp d e hd he)
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

theorem auxiliary_guarded_projection_probability_le
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p : Z → Point F) (l m : Z → Line F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | l x.2 ≠ m x.2 ∧ x.1 i ≠ (l x.2).1 ∧
        lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2)) ≠ p x.2 ∧
        OnLine (lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2))) (m x.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.auxiliary_next_event_probability_le K base noise hnoise i hi
    (fun z d => l z ≠ m z ∧ d ≠ (l z).1 ∧
      lineIntersection (l z) (lineThrough d (p z)) ≠ p z ∧
      OnLine (lineIntersection (l z) (lineThrough d (p z))) (m z)) (by
      intro z
      by_cases hne : l z = m z
      · simp [hne]
      · apply le_trans (Finset.card_le_card ?_)
          (card_projection_directions_le_one (InjectionExposure.remaining K base)
            (p z) (l z) (m z) hne)
        intro d hd
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.2⟩)
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

theorem inverse_token_budget_le_two_div (q b : ℕ) (hq : 0 < q) (hb : 10 * b ≤ q) :
    (1 : ℝ) / ((q + 1 - 5 * b : ℕ) : ℝ) ≤ 2 / (q : ℝ) := by
  have hd : 0 < q + 1 - 5 * b := by omega
  have hnum : q ≤ 2 * (q + 1 - 5 * b) := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hdr : (0 : ℝ) < (q + 1 - 5 * b : ℕ) := by exact_mod_cast hd
  apply (div_le_div_iff₀ hdr hqr).mpr
  simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using
    (show (q : ℝ) ≤ ((2 * (q + 1 - 5 * b) : ℕ) : ℝ) by exact_mod_cast hnum)

theorem inverse_remaining_le_two_div (q k b : ℕ) (hq : 0 < q)
    (hk : k ≤ 5 * b) (hb : 10 * b ≤ q) :
    (1 : ℝ) / ((q + 1 - k : ℕ) : ℝ) ≤ 2 / (q : ℝ) := by
  apply le_trans _ (inverse_token_budget_le_two_div q b hq hb)
  apply one_div_le_one_div_of_le
  · have hd : 0 < q + 1 - 5 * b := by omega
    exact_mod_cast hd
  · exact_mod_cast Nat.sub_le_sub_left hk (q + 1)

theorem auxiliary_guarded_joining_probability_le_two_div
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p r : Z → Point F) (b : ℕ)
    (hK : K.card ≤ 5 * b) (hb : 10 * b ≤ Fintype.card F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | p x.2 ≠ r x.2 ∧ OnLine (r x.2) (lineThrough (x.1 i) (p x.2))}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (auxiliary_guarded_joining_probability_le K base i hi noise hnoise p r).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

theorem auxiliary_guarded_projection_probability_le_two_div
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p : Z → Point F) (l m : Z → Line F) (b : ℕ)
    (hK : K.card ≤ 5 * b) (hb : 10 * b ≤ Fintype.card F) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | l x.2 ≠ m x.2 ∧ x.1 i ≠ (l x.2).1 ∧
        lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2)) ≠ p x.2 ∧
        OnLine (lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2))) (m x.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (auxiliary_guarded_projection_probability_le K base i hi noise hnoise p l m).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

end Balanced

end OAI
