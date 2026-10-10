import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaussianPropeller

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)

def IsPartition {d k : ℕ} (A : Fin k → Set (Space d)) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i

noncomputable def centroid {d : ℕ} (A : Set (Space d)) : Space d :=
  ∫ x in A, x ∂gaussian d

noncomputable def value {d k : ℕ} (A : Fin k → Set (Space d)) : ℝ :=
  ∑ i, ‖centroid (A i)‖ ^ 2

def coord {d : ℕ} (j : ℕ) (x : Space d) : ℝ :=
  if h : j < d then x ⟨j, h⟩ else 0

noncomputable def propeller (d k : ℕ) (i : Fin k) : Set (Space d) :=
  if i.val = 0 then {x | |coord 1 x| ≤ Real.sqrt 3 * coord 0 x}
  else if i.val = 1 then {x | 0 ≤ coord 1 x ∧ Real.sqrt 3 * coord 0 x ≤ coord 1 x}
  else if i.val = 2 then {x | coord 1 x ≤ 0 ∧ Real.sqrt 3 * coord 0 x ≤ -coord 1 x}
  else ∅

def AllPartitions : Prop :=
  (∀ (d k : ℕ), 0 < d → 0 < k → ∀ A : Fin k → Set (Space d),
    IsPartition A → value A ≤ 9 / (8 * Real.pi)) ∧
  (∀ (d k : ℕ), 2 ≤ d → 3 ≤ k →
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi))

theorem all_partitions : AllPartitions := by
  sorry

end GaussianPropeller

end OAI
