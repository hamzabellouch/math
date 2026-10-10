import OAI.Probability.InvariantIsing.Cavity.CavityTruncation

namespace OAI

/-! The dimension-dependent errors in the finite cavity comparison.
The geometric cutoff is retained with its full Gaussian amplitude. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityWeightedKernel (N : ℕ) (u K : ℕ → ℝ) : ℝ :=
  ∑ j : Fin N, perturbationWeight j ^ 2 * u j ^ 2 * K j

lemma cavityWeightedKernel_split (N n : ℕ) (u K : ℕ → ℝ) :
    cavityWeightedKernel (N + n) u K = cavityWeightedKernel N u K +
      ∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j) := by
  simp only [cavityWeightedKernel, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd]

lemma cavityWeightedKernel_abs_le (N : ℕ) (u K : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |cavityWeightedKernel N u K| ≤ 4 :=
  cavity_weighted_kernel_abs_le (fun j : Fin N => u j) (fun j : Fin N => K j)
    (fun j => hu j) (fun j => hK j)

lemma cavityWeightedKernel_difference (N : ℕ) (u K L : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) {d : ℝ} (hd : 0 ≤ d)
    (hKL : ∀ j, |K j - L j| ≤ ((j : ℝ) + 1) * d) :
    |cavityWeightedKernel N u K - cavityWeightedKernel N u L| ≤ 4 * d := by
  have hu2 (j : ℕ) : u j ^ 2 ≤ 4 := by
    have hh := abs_le.mp (hu j)
    nlinarith
  rw [cavityWeightedKernel, cavityWeightedKernel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |perturbationWeight j ^ 2 * u j ^ 2 * K j -
        perturbationWeight j ^ 2 * u j ^ 2 * L j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, 4 * d * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      calc
        _ ≤ (perturbationWeight j ^ 2 * 4) * (((j : ℝ) + 1) * d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hu2 j) (sq_nonneg _)) (hKL j)
            (abs_nonneg _) (by positivity)
        _ = (4 * d * perturbationWeight j) * (((j : ℝ) + 1) * perturbationWeight j) := by ring
        _ ≤ (4 * d * perturbationWeight j) * 1 :=
          mul_le_mul_of_nonneg_left (perturbationWeight_linear_le j)
            (mul_nonneg (mul_nonneg (by norm_num) hd) (perturbationWeight_nonneg j))
        _ = _ := mul_one _
    _ = (4 * d) * (1 - (1 / 2 : ℝ) ^ N) := by
      rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ 4 * d := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

theorem cavityWeightedKernel_amplitude_difference (N n : ℕ) (u K L : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) {d a b : ℝ}
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hKL : ∀ j, |K j - L j| ≤ ((j : ℝ) + 1) * d) :
    |b * cavityWeightedKernel (N + n) u K - a * cavityWeightedKernel N u L| ≤
      4 * |b - a| + 4 * a * d + 4 * b * (1 / 2 : ℝ) ^ N := by
  have hp := cavity_covariance_mass_difference (b := b) ha (cavityWeightedKernel_abs_le N u K hu hK)
    (cavityWeightedKernel_difference N u K L hu hd hKL)
  have ht := cavity_weighted_kernel_tail_le N n
    (fun j : Fin n => u (N + j)) (fun j : Fin n => K (N + j))
    (fun j => hu (N + j)) (fun j => hK (N + j))
  rw [cavityWeightedKernel_split]
  calc
    _ = |(b * cavityWeightedKernel N u K - a * cavityWeightedKernel N u L) +
        b * (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j))| :=
      by congr 1; ring
    _ ≤ |b * cavityWeightedKernel N u K - a * cavityWeightedKernel N u L| +
        |b * (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j))| :=
      abs_add_le _ _
    _ ≤ (4 * |b - a| + a * (4 * d)) + b * (4 * (1 / 2 : ℝ) ^ N) := by
      rw [abs_mul, abs_of_nonneg hb]
      exact add_le_add hp (mul_le_mul_of_nonneg_left ht hb)
    _ = _ := by ring

def cavityCovarianceRate (n : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
    4 * C * perturbationScale N ^ 2 +
    4 * ((N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)

lemma cavityCovarianceRate_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ cavityCovarianceRate n C N := by
  unfold cavityCovarianceRate
  positivity

lemma cavityCovarianceRate_tendsto (n : ℕ) (C : ℝ) :
    Tendsto (cavityCovarianceRate n C) atTop (𝓝 0) := by
  have he : Tendsto perturbationScale atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 / 16 : ℝ)) atTop (𝓝 0)
    simpa only [neg_div] using tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 16)
  have hs := (cavity_covariance_amplitude_increment_tendsto n).abs.const_mul 4
  have hm := (he.pow 2).const_mul (4 * C)
  have ht := (cavity_covariance_cutoff_error_tendsto n).const_mul 4
  have heq : cavityCovarianceRate n C = (fun N : ℕ =>
      4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
        (4 * C) * perturbationScale N ^ 2 +
        4 * ((N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)) := rfl
  rw [heq]
  simpa only [abs_zero, mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero] using (hs.add hm).add ht

end InvariantIsing

end

end OAI
