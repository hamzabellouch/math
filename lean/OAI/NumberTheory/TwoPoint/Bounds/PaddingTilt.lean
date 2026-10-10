import OAI.NumberTheory.TwoPoint.Bounds.PaddingPairSampling

namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingOriginalPrimeLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw Bool :=
  booleanLaw (1 / (p : ℝ)) (by positivity) (by
    apply (div_le_one (by exact_mod_cast (by omega : 0 < p))).mpr
    exact_mod_cast (by omega : 1 ≤ p))

noncomputable def paddingOriginalLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))

noncomputable def paddingTiltWeight (Q : Finset ℕ) (a : Q → Bool) : ℝ :=
  ∏ p : Q, if a p then 5 else 1

noncomputable def paddingTiltNormalizer (Q : Finset ℕ) : ℝ :=
  ∏ p : Q, (1 + 4 / (p : ℝ))

lemma paddingTiltWeight_pos (Q : Finset ℕ) (a : Q → Bool) : 0 < paddingTiltWeight Q a := by
  apply prod_pos
  intro p _
  cases a p <;> norm_num

lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity

lemma padding_prime_tilt (p : ℕ) (hp : 2 ≤ p) (a : Bool) :
    (paddingOriginalPrimeLaw p hp).weight a * (if a then 5 else 1) =
      (paddingAvailabilityLaw p hp).weight a * (1 + 4 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases a <;> simp only [paddingOriginalPrimeLaw, paddingAvailabilityLaw, booleanLaw,
    Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma padding_tilt_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (a : Q → Bool) :
    (paddingOriginalLaw Q hQ).weight a * paddingTiltWeight Q a =
      (paddingAvailableLaw Q hQ).weight a * paddingTiltNormalizer Q := by
  simp only [paddingOriginalLaw, paddingAvailableLaw, FiniteLaw.independent,
    paddingTiltWeight, paddingTiltNormalizer, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  exact padding_prime_tilt p (hQ p p.property) (a p)

lemma padding_tilt_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Bool) → ℝ) :
    (paddingOriginalLaw Q hQ).average (fun a => paddingTiltWeight Q a * F a) =
      paddingTiltNormalizer Q * (paddingAvailableLaw Q hQ).average F := by
  simp only [FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, padding_tilt_weight]
  ring

lemma padding_tilt_total (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (paddingOriginalLaw Q hQ).average (paddingTiltWeight Q) = paddingTiltNormalizer Q := by
  simpa using padding_tilt_average Q hQ (fun _ => 1)

noncomputable def paddingDivisorCoefficient (Q : Finset ℕ) (b : Q → Bool) : ℝ :=
  ∏ p : Q, if b p then 4 else 1

def PaddingSelectionSupported (Q : Finset ℕ) (a b : Q → Bool) : Prop :=
  ∀ p, b p = true → a p = true

lemma padding_selection_atom (a b : Bool) :
    (paddingSelectionLaw a).weight b * (if a then 5 else 1) =
      if b then (if a then 4 else 0) else 1 := by
  cases a <;> cases b <;> norm_num [paddingSelectionLaw, booleanLaw]

lemma padding_divisor_weight (Q : Finset ℕ) (a b : Q → Bool) :
    (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a =
      if PaddingSelectionSupported Q a b then paddingDivisorCoefficient Q b else 0 := by
  simp only [paddingDivisorLaw, FiniteLaw.independent, paddingTiltWeight,
    ← prod_mul_distrib, padding_selection_atom]
  by_cases hs : PaddingSelectionSupported Q a b
  · rw [ite_eq_left hs]
    unfold paddingDivisorCoefficient
    apply prod_congr rfl
    intro p _
    cases hb : b p
    · simp
    · simp [hs p hb]
  · rw [ite_eq_right hs]
    change ¬ ∀ p : Q, b p = true → a p = true at hs
    push Not at hs
    obtain ⟨p, hb, ha⟩ := hs
    apply prod_eq_zero (mem_univ p)
    simp [hb, ha]

lemma paddingDivisorLaw_weight_eq (Q : Finset ℕ) (a b : Q → Bool) :
    (paddingDivisorLaw Q a).weight b =
      if PaddingSelectionSupported Q a b then
        paddingDivisorCoefficient Q b / paddingTiltWeight Q a else 0 := by
  have hw := paddingTiltWeight_pos Q a
  have hh := padding_divisor_weight Q a b
  by_cases hs : PaddingSelectionSupported Q a b
  · rw [ite_eq_left hs] at hh ⊢
    exact (eq_div_iff hw.ne').mpr hh
  · rw [ite_eq_right hs] at hh ⊢
    exact (mul_eq_zero.mp hh).resolve_right hw.ne'

end TwoPointCorrelations

end OAI
