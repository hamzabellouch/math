import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPenalty
import OAI.Probability.InvariantIsing.Cavity.CavityBaseAmplitude

namespace OAI

/-! Extending a finite minimizing perturbation by the physical convention
adds only an exponentially small tail to its quadratic penalty. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseAmplitude_mem {N : ℕ} (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (j : ℕ) :
    cavityBaseAmplitude u j ∈ Set.Icc (1 : ℝ) 2 := by
  unfold cavityBaseAmplitude
  split_ifs with hj
  · exact hu ⟨j,hj⟩
  · norm_num

lemma cavityBaseAmplitude_penalty {N m n : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorMinimumPenalty (fun j : Fin (N+n) => cavityBaseAmplitude u j) v =
      tensorMinimumPenalty u v + (1/4:ℝ)*((1/2:ℝ)^N-(1/2:ℝ)^(N+n)) := by
  have hleft : (∑ j : Fin N, perturbationWeight j *
      (cavityBaseAmplitude u j - 3/2)^2) =
      ∑ j : Fin N, perturbationWeight j * (u j-3/2)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [cavityBaseAmplitude_fin]
  have hright : (∑ j : Fin n, perturbationWeight (Fin.natAdd N j) *
      (cavityBaseAmplitude u (Fin.natAdd N j) - 3/2)^2) =
      (1/4:ℝ) * ∑ j : Fin n, perturbationWeight (Fin.natAdd N j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : ¬(Fin.natAdd N j).val<N := by simp only [Fin.val_natAdd]; omega
    simp only [cavityBaseAmplitude, dite_eq_right hj]
    ring
  have hweight : (∑ j : Fin n, perturbationWeight (Fin.natAdd N j)) =
      (1/2:ℝ)^N-(1/2:ℝ)^(N+n) := by
    have hs := perturbationWeight_sum (N+n)
    rw [Fin.sum_univ_add] at hs
    have hl : (∑ j : Fin N, perturbationWeight (Fin.castAdd n j)) =
        1-(1/2:ℝ)^N := by simpa only [Fin.val_castAdd] using perturbationWeight_sum N
    rw [hl] at hs
    linarith
  unfold tensorMinimumPenalty
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd]
  rw [hleft, hright, hweight]
  ring

lemma cavityBaseAmplitude_penalty_le {N m n : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorMinimumPenalty (fun j : Fin (N+n) => cavityBaseAmplitude u j) v ≤
      tensorMinimumPenalty u v + (1/4:ℝ)*(1/2:ℝ)^N := by
  rw [cavityBaseAmplitude_penalty]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) (N+n)]

end InvariantIsing

end

end OAI
