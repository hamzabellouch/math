import OAI.Probability.InvariantIsing.Fields.SpinPriorContactMinimum

namespace OAI

/-! A joint constrained-prior minimum gives the two actual coordinate minima. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorPerturbationPressureMean_eq_namespaced {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v =
      (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        (fun j => enumeratedTreeDegree m j) h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates := by
  unfold spinPriorPerturbationPressureMean spinPriorMeanPressure
  ring

private lemma penalty_update {z : ℕ} (u w : Fin z → ℝ) (j : Fin z) (s : ℝ) :
    (∑ i, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      (∑ i, w i * (u i - 3 / 2) ^ 2) - w j * (u j - 3 / 2) ^ 2 + w j * (s - 3 / 2) ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      ∑ i ∈ Finset.univ.erase j, w i * (u i - 3 / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he, Function.update_self]
  ring

private lemma update_mem_Icc {z : ℕ} (u : Fin z → ℝ) (hu : ∀ i, u i ∈ Set.Icc (1 : ℝ) 2)
    (j : Fin z) (s : ℝ) (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    ∀ i, Function.update u j s i ∈ Set.Icc (1 : ℝ) 2 := by
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self] using hs
  · simpa only [Function.update_of_ne hi] using hu i

theorem spinPriorPerturbation_minimum_coordinates {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j∈Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') :
    let M := spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h
    (∀ (j : Fin N) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+perturbationWeight j*(u j-3/2)^2≤
        -M (Function.update u j s) v+perturbationWeight j*(s-3/2)^2) ∧
    (∀ (a : Fin m) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+(v a-3/2)^2≤-M u (Function.update v a s)+(s-3/2)^2) := by
  intro M
  constructor
  · intro j s hs
    have hc := hmin (Function.update u j s) v (update_mem_Icc u hu j s hs) hv
    unfold spinPriorPerturbationObjective at hc
    rw [penalty_update] at hc
    linarith
  · intro a s hs
    have hc := hmin u (Function.update v a s) hu (update_mem_Icc v hv a s hs)
    unfold spinPriorPerturbationObjective at hc
    have he := penalty_update v (fun _ => 1) a s
    simp only [one_mul] at he
    rw [he] at hc
    linarith

end InvariantIsing

end

end OAI
