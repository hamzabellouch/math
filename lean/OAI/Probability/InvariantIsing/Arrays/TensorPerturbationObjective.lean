import OAI.Probability.InvariantIsing.Arrays.FullPerturbationMinima

namespace OAI

/-! Global minima of the actual finite perturbation objective imply both
coordinate minimum conditions used by the GG estimates. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorPerturbationObjective {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -tensorPerturbationPressureMean μ eig c I u v t n b h +
    ∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2 + ∑ a, (v a - 3 / 2) ^ 2

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

/-- This is a direct restriction of the genuine joint finite-model minimum. -/
theorem tensorPerturbation_minimum_coordinates {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b h u v ≤ tensorPerturbationObjective μ eig c I t n b h u' v') :
    let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
    (∀ (j : Fin N) (s : ℝ), s ∈ Set.Icc (1 : ℝ) 2 →
      -M u v t + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
        -M (Function.update u j s) v t + perturbationWeight j * (s - 3 / 2) ^ 2) ∧
    (∀ (a : Fin m) (s : ℝ), s ∈ Set.Icc (1 : ℝ) 2 →
      -M u v t + (v a - 3 / 2) ^ 2 ≤ -M u (Function.update v a s) t + (s - 3 / 2) ^ 2) := by
  intro M
  constructor
  · intro j s hs
    have hc := hmin (Function.update u j s) v (update_mem_Icc u hu j s hs) hv
    unfold tensorPerturbationObjective at hc
    rw [penalty_update] at hc
    linarith
  · intro a s hs
    have hc := hmin u (Function.update v a s) hu (update_mem_Icc v hv a s hs)
    unfold tensorPerturbationObjective at hc
    have he := penalty_update v (fun _ => 1) a s
    simp only [one_mul] at he
    rw [he] at hc
    linarith

end InvariantIsing

end

end OAI
