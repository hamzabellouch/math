import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum
import OAI.Probability.InvariantIsing.Fields.PriorTensorNamespace

namespace OAI

/-! A joint constrained-prior minimum gives the two actual coordinate minima. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma priorPerturbationPressureMean_eq_namespaced {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    priorPerturbationPressureMean μ ν eig c I t h u v =
      (N : ℝ)⁻¹ * ∫ p, priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) n
          (fun j => enumeratedTreeDegree m j) h i) p ∂μ.prod gaussianCoordinates := by
  unfold priorPerturbationPressureMean
  congr 1
  symm
  exact (priorNamespacedLog_law μ ν _ c I _ _ _).integral_eq.trans
    (integral_map (measurable_priorTensorLog ν _ c I _ _ _).aemeasurable aestronglyMeasurable_id)

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

theorem priorPerturbation_minimum_coordinates {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j∈Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ ν eig c I t h u v≤priorPerturbationObjective μ ν eig c I t h u' v') :
    let M := priorPerturbationPressureMean μ ν eig c I t h
    (∀ (j : Fin N) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+perturbationWeight j*(u j-3/2)^2≤
        -M (Function.update u j s) v+perturbationWeight j*(s-3/2)^2) ∧
    (∀ (a : Fin m) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+(v a-3/2)^2≤-M u (Function.update v a s)+(s-3/2)^2) := by
  intro M
  constructor
  · intro j s hs
    have hc := hmin (Function.update u j s) v (update_mem_Icc u hu j s hs) hv
    unfold priorPerturbationObjective at hc
    rw [penalty_update] at hc
    linarith
  · intro a s hs
    have hc := hmin u (Function.update v a s) hu (update_mem_Icc v hv a s hs)
    unfold priorPerturbationObjective at hc
    have he := penalty_update v (fun _ => 1) a s
    simp only [one_mul] at he
    rw [he] at hc
    linarith

end InvariantIsing

end

end OAI
