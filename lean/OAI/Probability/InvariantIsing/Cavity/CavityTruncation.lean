import OAI.Probability.InvariantIsing.Cavity.CavityPerturbationRates
import OAI.Probability.InvariantIsing.Cavity.CavityPerturbationKernel

namespace OAI

/-! Uniform covariance bounds for the monomials omitted when the
perturbation cutoff changes by a fixed cavity size. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_weighted_kernel_abs_le {J : ℕ} (u K : Fin J → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |∑ j : Fin J, perturbationWeight j ^ 2 * u j ^ 2 * K j| ≤ 4 := by
  have hw (j : ℕ) : perturbationWeight j ^ 2 ≤ perturbationWeight j := by
    nlinarith [perturbationWeight_nonneg j, perturbationWeight_le_one j]
  calc
    _ ≤ ∑ j : Fin J, |perturbationWeight j ^ 2 * u j ^ 2 * K j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin J, 4 * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hu2 : u j ^ 2 ≤ 4 := by
        have hj := abs_le.mp (hu j)
        nlinarith
      rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc
        _ ≤ perturbationWeight j ^ 2 * u j ^ 2 :=
          mul_le_of_le_one_right (by positivity) (hK j)
        _ ≤ perturbationWeight j ^ 2 * 4 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)
        _ ≤ _ := by nlinarith [hw j]
    _ = 4 * (1 - (1 / 2 : ℝ) ^ J) := by rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ 4 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J]

lemma cavity_weighted_kernel_tail_le (N n : ℕ) (u K : Fin n → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u j ^ 2 * K j| ≤
      4 * (1 / 2 : ℝ) ^ N := by
  have hw (j : Fin n) : perturbationWeight (N + j) =
      (1 / 2 : ℝ) ^ N * perturbationWeight j := by
    unfold perturbationWeight
    rw [← pow_add]
    congr 1
  have he : (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u j ^ 2 * K j) =
      ((1 / 2 : ℝ) ^ N) ^ 2 * (∑ j : Fin n, perturbationWeight j ^ 2 * u j ^ 2 * K j) := by
    simp only [hw, mul_pow, Finset.mul_sum, mul_assoc]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((1 / 2 : ℝ) ^ N) ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left (cavity_weighted_kernel_abs_le u K hu hK) (sq_nonneg _)
    _ ≤ _ := by
      have h0 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N
      have h1 := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := N)
      nlinarith

lemma cavity_covariance_mass_difference {P Q a b δ : ℝ}
    (ha : 0 ≤ a) (hP : |P| ≤ 4) (hPQ : |P - Q| ≤ δ) :
    |b * P - a * Q| ≤ 4 * |b - a| + a * δ := by
  calc
    _ = |(b - a) * P + a * (P - Q)| := by congr 1; ring
    _ ≤ |(b - a) * P| + |a * (P - Q)| := abs_add_le _ _
    _ ≤ |b - a| * 4 + a * δ := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ ha)
    _ = _ := by ring

theorem cavity_covariance_cutoff_error_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + n) * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simp only [add_mul]
    simpa only [mul_zero, add_zero] using
      (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (n : ℝ))
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall (fun N => by positivity)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := perturbationScale_sq_le_one (N := N + n) (by omega)
    have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ N + n by positivity)
    exact (mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N))

end InvariantIsing

end

end OAI
