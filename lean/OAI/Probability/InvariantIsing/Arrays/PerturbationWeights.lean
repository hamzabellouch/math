import OAI.Probability.IsingPerceptron.JointGGClosure

namespace OAI

/-! Uniform finite perturbation sums for the manuscript's geometric weights. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma perturbationWeight_linear_le (j : ℕ) :
    ((j : ℝ) + 1) * perturbationWeight j ≤ 1 := by
  induction j with
  | zero => norm_num [perturbationWeight]
  | succ j ih =>
    have hw := perturbationWeight_nonneg j
    have he : perturbationWeight (j + 1) = perturbationWeight j / 2 := by
      unfold perturbationWeight
      rw [pow_succ]
      ring
    rw [he]
    push_cast
    nlinarith

lemma perturbationWeight_degree_sum_le {N m : ℕ} (degree : Fin N → Fin m → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    (∑ j : Fin N, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) ≤ D := by
  calc
    _ ≤ ∑ j : Fin N, D * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ perturbationWeight j ^ 2 * (D * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hdegree j) (sq_nonneg _)
        _ = (D * perturbationWeight j) * (((j : ℝ) + 1) * perturbationWeight j) := by ring
        _ ≤ (D * perturbationWeight j) * 1 := mul_le_mul_of_nonneg_left
          (perturbationWeight_linear_le j) (mul_nonneg hD (perturbationWeight_nonneg j))
        _ = _ := mul_one _
    _ = D * (1 - (1 / 2 : ℝ) ^ N) := by rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ D := mul_le_of_le_one_right hD (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

def tensorPerturbationAmplitude (N : ℕ) (u : Fin N → ℝ) (j : Fin N) : ℝ :=
  perturbationAmplitude N j * u j

lemma tensorPerturbationAmplitude_update {N : ℕ} (u : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    tensorPerturbationAmplitude N (Function.update u j t) =
      Function.update (tensorPerturbationAmplitude N u) j (perturbationAmplitude N j * t) := by
  classical
  funext i
  by_cases hi : i = j
  · subst i
    simp only [tensorPerturbationAmplitude, Function.update_self]
  · simp only [tensorPerturbationAmplitude, Function.update_of_ne hi]

lemma tensorPerturbationAmplitude_sq_le (N : ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (j : Fin N) :
    tensorPerturbationAmplitude N u j ^ 2 ≤
      4 * N * perturbationScale N ^ 2 * perturbationWeight j ^ 2 := by
  have hu2 : u j ^ 2 ≤ 4 := by
    have hb := abs_le.mp (hu j)
    nlinarith
  rw [tensorPerturbationAmplitude, mul_pow, perturbationAmplitude_sq]
  exact (mul_le_mul_of_nonneg_left hu2 (by positivity)).trans_eq (by ring)

lemma tensorPerturbationAmplitude_square_sum_le (N : ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) :
    (∑ j : Fin N, tensorPerturbationAmplitude N u j ^ 2) ≤ 4 * N * perturbationScale N ^ 2 := by
  calc
    _ ≤ ∑ j : Fin N, (4 * N * perturbationScale N ^ 2) * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hw : perturbationWeight j ^ 2 ≤ perturbationWeight j := by
        nlinarith [perturbationWeight_nonneg j, perturbationWeight_le_one j]
      exact (tensorPerturbationAmplitude_sq_le N u hu j).trans
        (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = (4 * N * perturbationScale N ^ 2) * (1 - (1 / 2 : ℝ) ^ N) := by
      rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Nat.succ_le_of_lt hN)
  · norm_num

lemma perturbationScale_sq_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ^ 2 ≤ 1 := by
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [perturbationScale_le_one hN]

/-- The fixed linear bound on the enumerated monomial degrees gives a
dimension-independent normalized rotation modulus. Only the finite sum
through dimension `N` is used. -/
theorem tensorPerturbationAmplitude_degree_sum_le {N m : ℕ}
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (degree : Fin N → Fin m → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    (∑ j : Fin N, tensorPerturbationAmplitude N u j ^ 2 * ∑ a, (degree j a : ℝ)) ≤
      4 * N * perturbationScale N ^ 2 * D := by
  calc
    _ ≤ ∑ j : Fin N, (4 * N * perturbationScale N ^ 2 * perturbationWeight j ^ 2) *
        ∑ a, (degree j a : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (tensorPerturbationAmplitude_sq_le N u hu j)
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = (4 * N * perturbationScale N ^ 2) *
        ∑ j : Fin N, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (perturbationWeight_degree_sum_le degree D hD hdegree)
      (by positivity)

end InvariantIsing

end

end OAI
