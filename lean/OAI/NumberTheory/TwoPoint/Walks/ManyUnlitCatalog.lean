import OAI.NumberTheory.TwoPoint.Walks.ManyUnlitDecay
import OAI.NumberTheory.TwoPoint.Bounds.DivisorWordMajorant

namespace OAI

/-! Sum a finite actual designation catalog with varying extra reciprocal exponents. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_many_unlit_catalog {I : Type*} [Fintype I]
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : I → ℕ) (H : ℝ) (weight : I → ℝ),
      (∀ i, 0 ≤ weight i) →
      (∑ i, weight i) ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      (∀ i, L ^ (1 / 50 : ℝ) ≤ 2 * E i) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∑ i, weight i * (H⁻¹) ^ E i) ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_many_unlit_decay C hC] with L hdecay
  intro E H weight hw hsum hE hH
  let scale := Real.exp (C * L * (Real.log L) ^ 2)
  let target := Real.exp (-L ^ (101 / 100 : ℝ))
  have hscale : 0 < scale := Real.exp_pos _
  have htarget : 0 ≤ target / scale := by positivity
  have hi (i : I) : (H⁻¹) ^ E i ≤ target / scale := by
    apply (le_div_iff₀ hscale).mpr
    simpa only [mul_comm] using hdecay (E i) H (hE i) hH
  calc
    _ ≤ ∑ i, weight i * (target / scale) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hw i))
    _ = (∑ i, weight i) * (target / scale) := (sum_mul _ _ _).symm
    _ ≤ scale * (target / scale) := mul_le_mul_of_nonneg_right hsum htarget
    _ = target := mul_div_cancel₀ _ hscale.ne'

/-- The input is the literal unlit set in each word's nonsingleton
expansion. The exponent is derived from those occurrences internally. -/
theorem eventually_many_unlit_designations {I ι τ : Type*}
    [Fintype I] [Fintype ι] [Fintype τ] [DecidableEq ι]
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (label : I → τ → ι) (U : I → Finset τ)
      (H : ℝ) (weight : I → ℝ),
      (∀ i, U i ⊆ nonsingletonSlots (label i)) →
      (∀ i, L ^ (1 / 50 : ℝ) < (U i).card) →
      (∀ i, 0 ≤ weight i) →
      (∑ i, weight i) ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∑ i, weight i * (H⁻¹) ^
        (∑ a ∈ nonsingletonLabels (label i),
          extraReciprocalExponent (litOccurrences (label i) (designationLit (U i)) a).card
            (unlitOccurrences (label i) (designationLit (U i)) a).card)) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_many_unlit_catalog (I := I) C hC] with L h
  intro label U H weight hU hlarge hw hsum hH
  apply h _ H weight hw hsum ?_ hH
  intro i
  have he := designation_card_le_twice_extra (label i) (U i) (hU i)
  have he' : ((U i).card : ℝ) ≤ 2 *
      (∑ a ∈ nonsingletonLabels (label i),
        extraReciprocalExponent (litOccurrences (label i) (designationLit (U i)) a).card
          (unlitOccurrences (label i) (designationLit (U i)) a).card) := by exact_mod_cast he
  exact (hlarge i).le.trans he'

end TwoPointCorrelations

end OAI
