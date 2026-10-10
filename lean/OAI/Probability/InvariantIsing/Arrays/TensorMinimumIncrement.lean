import OAI.Probability.InvariantIsing.Cavity.CavityAmplitudePenalty

namespace OAI

/-! The actual minimum envelopes satisfy the physical finite-volume pressure
increment inequality, with only the vanishing quadratic penalty loss. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensor_minimum_increment {N n m depth : ℕ}
    (μ : Measure (SpecialOrthogonal (N+n))) (ν : Measure (SpecialOrthogonal N))
    (eigF cF : Fin (N+n) → ℝ) (eigB cB : Fin N → ℝ)
    (IF : Fin m → Finset (Fin (N+n))) (IB : Fin m → Finset (Fin N))
    (t : ℝ) (b h : ℕ → ℝ) (uF : Fin (N+n) → ℝ) (vF : Fin m → ℝ)
    (uB : Fin N → ℝ) (vB : Fin m → ℝ)
    (huB : ∀ j, uB j ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eigF cF IF t depth b h uF vF ≤
        tensorPerturbationObjective μ eigF cF IF t depth b h u' v') :
    let uE := fun j : Fin (N+n) => cavityBaseAmplitude uB j;
    -(N+n : ℝ)*tensorPerturbationObjective μ eigF cF IF t depth b h uF vF +
      (N : ℝ)*tensorPerturbationObjective ν eigB cB IB t depth b h uB vB ≥
    ((N+n : ℝ)*tensorPerturbationPressureMean μ eigF cF IF uE vB t depth b h -
      (N : ℝ)*tensorPerturbationPressureMean ν eigB cB IB uB vB t depth b h) -
      (n : ℝ)*tensorMinimumPenalty uB vB - (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N := by
  intro uE
  have hm := hminF uE vB (fun j => cavityBaseAmplitude_mem uB huB j) hvB
  simp only [tensorPerturbationObjective_eq] at hm
  have hp := cavityBaseAmplitude_penalty_le (n := n) uB vB
  have hscale := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ)≤N+n)
  have hpscale := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤N+n)
  simp only [tensorPerturbationObjective_eq]
  dsimp only [uE] at hscale ⊢
  nlinarith

end InvariantIsing

end

end OAI
