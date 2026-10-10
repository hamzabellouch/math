import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights
import OAI.Probability.InvariantIsing.Arrays.PerturbationFeatures

namespace OAI

/-! The overlap modulus of the finite Gaussian perturbation covariance.
The geometric weights absorb the enumerated monomial degrees. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_monomial_difference {m : ℕ} (A B : Fin m → ℝ) (d : Fin m → ℕ)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1)
    {δ : ℝ} (hd : ∀ a, |A a - B a| ≤ δ) :
    |(∏ a, A a ^ d a) - ∏ a, B a ^ d a| ≤ (∑ a, (d a : ℝ)) * δ := by
  have hp (a : Fin m) : |A a ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hA a)
  have hq (a : Fin m) : |B a ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hB a)
  calc
    _ ≤ ∑ a, |A a ^ d a - B a ^ d a| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hp a) (fun a _ => hq a)
    _ ≤ ∑ a, (d a : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_pow_sub_pow_le_degree (hA a) (hB a) (d a)).trans
        (mul_le_mul_of_nonneg_left (hd a) (Nat.cast_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma cavity_monomial_abs_le {m : ℕ} (A : Fin m → ℝ) (d : Fin m → ℕ)
    (hA : ∀ a, |A a| ≤ 1) : |∏ a, A a ^ d a| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun a _ => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hA a))

/-- The common tree coordinate does not enlarge the overlap error. -/
lemma cavity_spectral_tree_kernel_difference {m : ℕ}
    (A B : Fin m → ℝ) (d : Fin m → ℕ) (r : ℕ) (q : ℝ)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1) (hq : |q| ≤ 1)
    {δ : ℝ} (hd : ∀ a, |A a - B a| ≤ δ) :
    |(∏ a, A a ^ d a) * q ^ r - (∏ a, B a ^ d a) * q ^ r| ≤
      (∑ a, (d a : ℝ)) * δ := by
  rw [← sub_mul, abs_mul]
  have hqr : |q ^ r| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hq
  exact (mul_le_mul_of_nonneg_left hqr (abs_nonneg _)).trans
    (by simpa only [mul_one] using cavity_monomial_difference A B d hA hB hd)

/-- Degree-weighted covariance errors are bounded independently of the
number of perturbation monomials retained. -/
theorem cavity_weighted_covariance_difference {J m : ℕ}
    (A B : Fin m → ℝ) (degree : Fin J → Fin m → ℕ) (r : Fin J → ℕ) (q : ℝ)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1) (hq : |q| ≤ 1)
    {δ D : ℝ} (hδ : 0 ≤ δ) (hd : ∀ a, |A a - B a| ≤ δ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    |(∑ j : Fin J, perturbationWeight j ^ 2 * ((∏ a, A a ^ degree j a) * q ^ r j)) -
      ∑ j : Fin J, perturbationWeight j ^ 2 * ((∏ a, B a ^ degree j a) * q ^ r j)| ≤
      D * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin J, |perturbationWeight j ^ 2 * ((∏ a, A a ^ degree j a) * q ^ r j) -
        perturbationWeight j ^ 2 * ((∏ a, B a ^ degree j a) * q ^ r j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin J, (perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) * δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (cavity_spectral_tree_kernel_difference A B (degree j) (r j) q hA hB hq hd)
        (sq_nonneg (perturbationWeight j))
    _ = (∑ j : Fin J, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) * δ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ D * δ := mul_le_mul_of_nonneg_right
      (perturbationWeight_degree_sum_le degree D hD hdegree) hδ

/-- The actual coefficient bound `|u_j| ≤ 2` contributes a factor four. -/
theorem cavity_weighted_covariance_difference_amplitude {J m : ℕ}
    (A B : Fin m → ℝ) (degree : Fin J → Fin m → ℕ) (r : Fin J → ℕ) (q : ℝ)
    (u : Fin J → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1) (hq : |q| ≤ 1)
    {δ D : ℝ} (hδ : 0 ≤ δ) (hd : ∀ a, |A a - B a| ≤ δ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    |(∑ j : Fin J, perturbationWeight j ^ 2 * u j ^ 2 * ((∏ a, A a ^ degree j a) * q ^ r j)) -
      ∑ j : Fin J, perturbationWeight j ^ 2 * u j ^ 2 * ((∏ a, B a ^ degree j a) * q ^ r j)| ≤
      4 * D * δ := by
  have hu2 (j : Fin J) : u j ^ 2 ≤ 4 := by
    have hj := abs_le.mp (hu j)
    nlinarith
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin J, |perturbationWeight j ^ 2 * u j ^ 2 * ((∏ a, A a ^ degree j a) * q ^ r j) -
        perturbationWeight j ^ 2 * u j ^ 2 * ((∏ a, B a ^ degree j a) * q ^ r j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin J, (4 * perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) * δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hdj := cavity_spectral_tree_kernel_difference A B (degree j) (r j) q hA hB hq hd
      calc
        _ ≤ (perturbationWeight j ^ 2 * u j ^ 2) * ((∑ a, (degree j a : ℝ)) * δ) :=
          mul_le_mul_of_nonneg_left hdj (by positivity)
        _ ≤ (perturbationWeight j ^ 2 * 4) * ((∑ a, (degree j a : ℝ)) * δ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hu2 j) (sq_nonneg _)) (by positivity)
        _ = _ := by ring
    _ = 4 * (∑ j : Fin J, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) * δ := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ 4 * D * δ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (perturbationWeight_degree_sum_le degree D hD hdegree)
        (by norm_num)) hδ

end InvariantIsing

end

end OAI
