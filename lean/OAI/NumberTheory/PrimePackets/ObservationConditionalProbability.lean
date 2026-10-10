import OAI.NumberTheory.PrimePackets.ConditionalOrbitEntropy

namespace OAI

/-!
# Conditional probabilities of finite observations

The conditional entropy is the integral of the entropy of the actual
finite conditional distributions. Zero-mass conditioning cells contribute
zero, without requiring arbitrary probability distributions on them.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]

def observationConditionalProbability (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (a : α) (y : Y) : ℝ :=
  μ.real {z | (Q z,P z) = (Q y,a)} / μ.real {z | Q z = Q y}

omit [Fintype α] [Fintype β] in
lemma observationConditionalProbability_nonneg
    (μ : Measure Y) (P : Y → α) (Q : Y → β) (a : α) (y : Y) :
    0 ≤ observationConditionalProbability μ P Q a y :=
  div_nonneg measureReal_nonneg measureReal_nonneg

omit [Fintype α] [Fintype β] in
lemma observationConditionalProbability_le_one
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β) (a : α) (y : Y) :
    observationConditionalProbability μ P Q a y ≤ 1 := by
  unfold observationConditionalProbability
  by_cases h : μ.real {z | Q z = Q y} = 0
  · simp [h]
  apply (div_le_one₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm h))).mpr
  exact measureReal_mono (fun z hz => congrArg Prod.fst hz) (measure_ne_top _ _)

omit [Fintype β] in
lemma observationConditionalProbability_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    {y : Y} (hy : μ {z | Q z = Q y} ≠ 0) :
    ∑ a, observationConditionalProbability μ P Q a y = 1 := by
  have hr : μ.real {z | Q z = Q y} ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hy,measure_ne_top _ _⟩
  simp only [observationConditionalProbability, ← Finset.sum_div,
    observation_joint_row μ Q P hQ hP, div_self hr]

lemma observationConditionalProbability_ae_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    ∀ᵐ y ∂μ, ∑ a, observationConditionalProbability μ P Q a y = 1 := by
  filter_upwards [ae_nonnull_fiber μ Q] with y hy
  exact observationConditionalProbability_sum μ P Q hP hQ hy

theorem conditionalObservationEntropy_eq_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q =
      ∑ b, μ.real {y | Q y = b} *
        finiteShannon (fun a => μ.real {y | (Q y,P y) = (b,a)} /
          μ.real {y | Q y = b}) := by
  have H := finiteShannon_joint_decomposition
    (fun z : β × α => μ.real {y | (Q y,P y) = z}) (fun _ => measureReal_nonneg)
  simp only [observation_joint_row μ Q P hQ hP] at H
  unfold conditionalObservationEntropy observationEntropy
  linarith

theorem conditionalObservationEntropy_eq_integral
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q =
      ∫ y, finiteShannon (fun a => observationConditionalProbability μ P Q a y) ∂μ := by
  rw [conditionalObservationEntropy_eq_sum μ P Q hP hQ]
  symm
  exact integral_finite_values μ Q hQ (fun b => finiteShannon (fun a =>
    μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b}))

end PrimeDegreePackets

end

end OAI
