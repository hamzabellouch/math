import OAI.Probability.InvariantIsing.Fields.PriorMinimumEnvelope
import OAI.Probability.InvariantIsing.Cavity.CavityAmplitudePenalty

namespace OAI

/-! Physical increments of the fixed-prior minimum envelope. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem prior_minimum_increment {N n m depth : ℕ}
    (μ : Measure (SpecialOrthogonal (N+n))) (ν : Measure (SpecialOrthogonal N))
    (ρF : Measure (Spin (N+n) × LabeledLeaf depth)) (ρB : Measure (Spin N × LabeledLeaf depth))
    (eigF cF : Fin (N+n) → ℝ) (eigB cB : Fin N → ℝ)
    (IF : Fin m → Finset (Fin (N+n))) (IB : Fin m → Finset (Fin N))
    (t : ℝ) (h : ℕ → ℝ) (uF : Fin (N+n) → ℝ) (vF : Fin m → ℝ)
    (uB : Fin N → ℝ) (vB : Fin m → ℝ)
    (huB : ∀ j, uB j ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ ρF eigF cF IF t h uF vF ≤
        priorPerturbationObjective μ ρF eigF cF IF t h u' v') :
    let uE := fun j : Fin (N+n) => cavityBaseAmplitude uB j;
    -(N+n : ℝ)*priorPerturbationObjective μ ρF eigF cF IF t h uF vF +
      (N : ℝ)*priorPerturbationObjective ν ρB eigB cB IB t h uB vB ≥
    ((N+n : ℝ)*priorPerturbationPressureMean μ ρF eigF cF IF t h uE vB -
      (N : ℝ)*priorPerturbationPressureMean ν ρB eigB cB IB t h uB vB) -
      (n : ℝ)*tensorMinimumPenalty uB vB - (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N := by
  intro uE
  have hm := hminF uE vB (fun j => cavityBaseAmplitude_mem uB huB j) hvB
  simp only [priorPerturbationObjective_eq] at hm
  have hp := cavityBaseAmplitude_penalty_le (n := n) uB vB
  have hscale := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ)≤N+n)
  have hpscale := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤N+n)
  simp only [priorPerturbationObjective_eq]
  dsimp only [uE] at hscale ⊢
  nlinarith

end InvariantIsing

end

end OAI
