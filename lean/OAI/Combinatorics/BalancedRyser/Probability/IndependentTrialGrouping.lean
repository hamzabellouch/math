import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialKernel

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  {μ : Measure Ω} {ξ : (i : Fin T) → Ω → A i}

theorem past_independent_current
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun (fun ω (j : {j : Fin T // j.val < i.val}) ↦ ξ j ω) (ξ i) μ := by
  have h := independent_predicate_blocks (fun j : Fin T ↦ j.val < i.val) hξ hind
  exact h.comp measurable_id (measurable_pi_apply ⟨i, lt_irrefl i.val⟩)

theorem pastCurrent_independent_future
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun
      (fun ω ↦ ((fun j : {j : Fin T // j.val < i.val} ↦ ξ j ω), ξ i ω))
      (fun ω (j : {j : Fin T // i.val < j.val}) ↦ ξ j ω) μ := by
  have h := independent_predicate_blocks (fun j : Fin T ↦ j.val ≤ i.val) hξ hind
  let left : ((j : {j : Fin T // j.val ≤ i.val}) → A j) →
      (((j : {j : Fin T // j.val < i.val}) → A j) × A i) :=
    fun x ↦ ((fun j ↦ x ⟨j.val, le_of_lt j.property⟩), x ⟨i, le_rfl⟩)
  let right : ((j : {j : Fin T // ¬j.val ≤ i.val}) → A j) →
      ((j : {j : Fin T // i.val < j.val}) → A j) :=
    fun x j ↦ x ⟨j.val, not_le_of_gt j.property⟩
  have hl : Measurable left :=
    (Measurable.of_eval (fun index ↦ measurable_pi_apply
      (⟨index.val, le_of_lt index.property⟩ : {j : Fin T // j.val ≤ i.val}))).prodMk
        (measurable_pi_apply (⟨i, le_rfl⟩ : {j : Fin T // j.val ≤ i.val}))
  have hr : Measurable right :=
    Measurable.of_eval (fun index ↦ measurable_pi_apply
      (⟨index.val, not_le_of_gt index.property⟩ : {j : Fin T // ¬j.val ≤ i.val}))
  exact h.comp hl hr

theorem independent_past_current
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun (fun ω (j : {j : Fin T // j.val < i.val}) ↦ ξ j ω) (ξ i) μ :=
  past_independent_current hξ hind i

theorem independent_past_current_future
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun
      (fun ω ↦ ((fun j : {j : Fin T // j.val < i.val} ↦ ξ j ω), ξ i ω))
      (fun ω (j : {j : Fin T // i.val < j.val}) ↦ ξ j ω) μ :=
  pastCurrent_independent_future hξ hind i

end Balanced.IndependentTrials

end OAI
