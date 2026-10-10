import OAI.NumberTheory.TwoPoint.Bounds.CenteredWordExpansion

namespace OAI

/-! Apply exact uniform singleton centering to the complete signed word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma uniform_singleton_target_lt (B : ℕ) (p : ι → ℕ) (label : τ → ι)
    (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t)) (i : ι)
    (hi : i ∈ singletonLabels label) :
    (singletonTarget label target base i).val < p i := by
  simp only [singletonTarget, dite_eq_left hi]
  simpa only [singletonRepresentative_label] using
    htarget (singletonRepresentative label ⟨i, hi⟩)

/-- Contradictory lit tests vanish even with all singleton factors retained. -/
lemma uniform_word_designation_zero (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t)) (U : Finset τ)
    (R : ℝ) (G : (ι → Fin B) → ℝ)
    (hL : ¬LitConsistent (nonsingletonSlots label \ U) label target) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) *
        ((∏ t ∈ nonsingletonSlots label \ U,
          if x (label t) = target t then (1 : ℝ) else 0) *
          ((∏ i ∈ singletonLabels label,
            ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) -
              (p i : ℝ)⁻¹)) * G x))) = 0 := by
  have hprod (x : ι → Fin B) :
      (∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) -
          (uniformResidueLaw B (p i) (hp i) (hpB i)).weight
            (singletonTarget label target base i))) =
        ∏ i ∈ singletonLabels label,
          ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro i hi
    rw [uniformResidueLaw_weight B (p i) (hp i) (hpB i) _
      (uniform_singleton_target_lt B p label target base htarget i hi)]
  have hz := designated_residue_zero
    (fun i => uniformResidueLaw B (p i) (hp i) (hpB i)) (singletonLabels label)
    (nonsingletonSlots label \ U) label target (singletonTarget label target base)
    (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) G hL
  simpa only [hprod] using hz

/-- Full-word majorant. Absolute values are introduced only after the
signed expansion and exact singleton integrations have been performed. -/
theorem uniform_centered_word_majorant (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R : ℝ) (hR : 0 ≤ R) (G : (ι → Fin B) → ℝ) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        if LitConsistent (nonsingletonSlots label \ U) label target then
          R * designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
            (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
              (fun x => |selectedMixedDifference (singletonLabels label)
                (singletonTarget label target base)
                (fun x => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                  (litForcedTarget (nonsingletonSlots label \ U) label target base) x)) x|)
        else 0 := by
  rw [centered_word_expectation _ label target base (fun i => (p i : ℝ)⁻¹) R G]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro U _
  by_cases hL : LitConsistent (nonsingletonSlots label \ U) label target
  · rw [ite_eq_left hL]
    exact uniform_designated_trace_bound B p hp hpB (singletonLabels label)
      (nonsingletonSlots label \ U) U label target (singletonTarget label target base) base
      R G hR hL (singleton_disjoint_designated label U)
      (uniform_singleton_target_lt B p label target base htarget)
      (fun t _ => htarget t)
  · rw [ite_eq_right hL,
      uniform_word_designation_zero B p hp hpB label target base htarget U R G hL, abs_zero]

/-- The crude mixed-difference bound can be used after the signed
singleton integration, retaining every exact reciprocal coefficient. -/
theorem uniform_centered_word_crude_bound (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R : ℝ) (hR : 0 ≤ R) (G : (ι → Fin B) → ℝ) (hG : ∀ x, |G x| ≤ 1) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        R * designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
          2 ^ (singletonLabels label).card := by
  apply (uniform_centered_word_majorant B p hp hpB label target base htarget R hR G).trans
  apply sum_le_sum
  intro U _
  have hcoef : 0 ≤ R * designatedReciprocal p (singletonLabels label)
      (nonsingletonSlots label \ U) U label := by
    unfold designatedReciprocal
    positivity
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ hcoef
    apply (FiniteLaw.average_mono _ (fun x =>
      selectedMixedDifference_bound (singletonLabels label) (singletonTarget label target base)
        _ (fun y => hG _) x)).trans_eq
    exact FiniteLaw.average_const _ _
  · exact mul_nonneg hcoef (by positivity)

end TwoPointCorrelations

end OAI
