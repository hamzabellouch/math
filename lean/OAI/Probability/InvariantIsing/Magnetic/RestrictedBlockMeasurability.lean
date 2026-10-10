import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockSpinEvaluation

namespace OAI

/-! Joint measurability of the original constrained block spin test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_restrictedFieldBlockSpinIntegrand {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        restrictedFieldBlockSpinIntegrand S hS h p.1 p.2 q Φ) := by
  have he : (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        restrictedFieldBlockSpinIntegrand S hS h p.1 p.2 q Φ) =
      fun p => (N : ℝ)⁻¹ * ∑ j, restrictedFieldSpinPairIntegrand S hS h p.1 p.2 q Φ j := by
    funext p
    exact restrictedFieldBlockSpinIntegrand_eq_sum S hS h _ _ q Φ hΦ
  rw [he]
  exact (Finset.measurable_sum _ (fun j _ => measurable_restrictedFieldSpinPairIntegrand S hS h q Φ j)).const_mul _

lemma measurable_restrictedFieldBlockSpinMean {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    Measurable (fun z => restrictedFieldBlockSpinMean S hS h z q Φ) :=
  (measurable_restrictedFieldBlockSpinIntegrand S hS h q Φ hΦ).stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
