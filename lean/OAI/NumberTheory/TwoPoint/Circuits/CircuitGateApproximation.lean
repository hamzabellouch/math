import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateFailure

namespace OAI

/-! A single fixed polynomial approximates an arbitrarily wide AND gate
under any supplied finite input law. The sampling and its error bound are
explicit, and the polynomial degree is bounded by the number of sampled
linear factors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_mono {α : Type*} [Fintype α]
    (μ : FiniteLaw α) {E F : α → Prop} (h : ∀ x, E x → F x) :
    μ.probability E ≤ μ.probability F := by
  unfold FiniteLaw.probability
  apply μ.average_mono
  intro x
  by_cases he : E x
  · simp [he, h x he]
  · simp [he]
    split_ifs <;> norm_num

theorem gate_pointwise_failure (k s : ℕ) (b : Fin k → Bool) :
    (gateSamplingLaw k k s).probability (fun x =>
      sampledAndPolynomial x (fun i => if b i then 1 else 0) ≠ boolAndValue b) ≤
        (7 / 8 : ℝ) ^ s := by
  by_cases hb : ∀ i, b i = true
  · have he (x : GateSamplingChoices k k s) :
        sampledAndPolynomial x (fun i => if b i then 1 else 0) = boolAndValue b := by
      rw [sampledAndPolynomial_all_true x b hb]
      unfold boolAndValue
      rw [ite_eq_left hb]
    have hz : (gateSamplingLaw k k s).probability (fun x =>
        sampledAndPolynomial x (fun i => if b i then 1 else 0) ≠ boolAndValue b) = 0 := by
      unfold FiniteLaw.probability
      simp only [he, ne_eq, not_true_eq_false, ite_false]
      exact FiniteLaw.average_const _ 0
    rw [hz]
    positivity
  · have hnonempty : (falseCoordinates b).Nonempty := by
      push Not at hb
      obtain ⟨i, hi⟩ := hb
      refine ⟨i, ?_⟩
      simp only [falseCoordinates, mem_filter, mem_univ, true_and]
      cases hbi : b i <;> simp_all
    have hcard : (falseCoordinates b).card ≤ k := by
      exact (card_le_card (filter_subset _ _)).trans_eq (card_fin k)
    exact ((gateSamplingLaw k k s).probability_mono
      (fun x hx => sampledAndPolynomial_failure x b hx)).trans
        (gateSamplingLaw_failure k k s (falseCoordinates b) hnonempty hcard)

/-- The probabilistic method fixes all samples simultaneously for the input
law, without imposing a condition on that law. -/
theorem exists_and_gate_approximation {α : Type*} [Fintype α]
    (ν : FiniteLaw α) (k s : ℕ) (b : α → Fin k → Bool) :
    ∃ x : GateSamplingChoices k k s,
      ν.probability (fun y =>
        sampledAndPolynomial x (fun i => if b y i then 1 else 0) ≠ boolAndValue (b y)) ≤
          (7 / 8 : ℝ) ^ s := by
  exact exists_choice_of_pointwise_failure (gateSamplingLaw k k s) ν _
    (fun y => gate_pointwise_failure k s (b y))

end TwoPointCorrelations

end OAI
