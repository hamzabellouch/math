import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum
import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPenalty

namespace OAI

/-! Minimum envelopes for the actual fixed-prior model. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma priorPerturbationObjective_eq {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    priorPerturbationObjective μ ν eig c I t h u v =
      -priorPerturbationPressureMean μ ν eig c I t h u v + tensorMinimumPenalty u v := by
  unfold priorPerturbationObjective tensorMinimumPenalty
  ring

/-- A genuine minimum lies within the same uniform cost of the base pressure,
and its quadratic penalty is at most twice that cost. -/
theorem prior_minimum_envelope_cost {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ ν eig c I t h u v ≤
        priorPerturbationObjective μ ν eig c I t h u' v')
    (P δ : ℝ)
    (hcost : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      |priorPerturbationPressureMean μ ν eig c I t h u' v' - P| ≤ δ) :
    |(-priorPerturbationObjective μ ν eig c I t h u v) - P| ≤ δ ∧
      tensorMinimumPenalty u v ≤ 2 * δ := by
  have hcenter : ∀ j : Fin N, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hcenter' : ∀ a : Fin m, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hc := abs_le.mp (hcost _ _ hcenter hcenter')
  have hp := abs_le.mp (hcost u v hu hv)
  have hm := hmin _ _ hcenter hcenter'
  rw [priorPerturbationObjective_eq, priorPerturbationObjective_eq,
    tensorMinimumPenalty_center] at hm
  have hn := tensorMinimumPenalty_nonneg u v
  rw [priorPerturbationObjective_eq]
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

end InvariantIsing

end

end OAI
