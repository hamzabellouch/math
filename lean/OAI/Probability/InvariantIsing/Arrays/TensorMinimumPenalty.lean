import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationObjective

namespace OAI

/-! The actual minimizing objective has a vanishing penalty whenever its
pressure has a uniform vanishing perturbation cost. Its negative minimum
is the scalar pressure envelope used in the cavity telescoping argument. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorMinimumPenalty {N m : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  (∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2) + ∑ a, (v a - 3 / 2) ^ 2

lemma tensorMinimumPenalty_nonneg {N m : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    0 ≤ tensorMinimumPenalty u v :=
  add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (perturbationWeight_nonneg j)
    (sq_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma tensorMinimumPenalty_center (N m : ℕ) :
    tensorMinimumPenalty (fun _ : Fin N => (3 : ℝ)/2) (fun _ : Fin m => (3 : ℝ)/2) = 0 := by
  simp [tensorMinimumPenalty]

lemma tensorPerturbationObjective_eq {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorPerturbationObjective μ eig c I t n b h u v =
      -tensorPerturbationPressureMean μ eig c I u v t n b h + tensorMinimumPenalty u v := by
  unfold tensorPerturbationObjective tensorMinimumPenalty
  ring

/-- A genuine minimum lies within the same uniform cost of the base pressure,
and its quadratic penalty is at most twice that cost. -/
theorem tensor_minimum_envelope_cost {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b h u v ≤
        tensorPerturbationObjective μ eig c I t n b h u' v')
    (P δ : ℝ)
    (hcost : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      |tensorPerturbationPressureMean μ eig c I u' v' t n b h - P| ≤ δ) :
    |(-tensorPerturbationObjective μ eig c I t n b h u v) - P| ≤ δ ∧
      tensorMinimumPenalty u v ≤ 2 * δ := by
  have hcenter : ∀ j : Fin N, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hcenter' : ∀ a : Fin m, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hc := abs_le.mp (hcost _ _ hcenter hcenter')
  have hp := abs_le.mp (hcost u v hu hv)
  have hm := hmin _ _ hcenter hcenter'
  rw [tensorPerturbationObjective_eq, tensorPerturbationObjective_eq,
    tensorMinimumPenalty_center] at hm
  have hn := tensorMinimumPenalty_nonneg u v
  rw [tensorPerturbationObjective_eq]
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

end InvariantIsing

end

end OAI
