import OAI.Probability.InvariantIsing.Cavity.CavityPerturbationRates
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation

namespace OAI

/-! The deterministic perturbation error under a fixed cavity-size
jump, stated for the actual spectral-diagonal perturbation energy. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_weighted_overlap_sum_abs {m : ℕ} (v q : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (hq : ∀ a, |q a| ≤ 1) :
    |∑ a, v a * q a| ≤ 2 * m := by
  calc
    _ ≤ ∑ a, |v a * q a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact (mul_le_mul (hv a) (hq a) (abs_nonneg _) (by norm_num)).trans_eq (mul_one 2)
    _ = _ := by simp; ring

lemma cavity_weighted_overlap_sum_difference {m : ℕ} (v q r : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) {δ : ℝ} (herr : ∀ a, |q a - r a| ≤ δ) :
    |(∑ a, v a * q a) - ∑ a, v a * r a| ≤ 2 * m * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |v a * q a - v a * r a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, 2 * δ := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hv a) (herr a) (abs_nonneg _) (by norm_num)
    _ = _ := by simp; ring

theorem cavity_diagonal_perturbation_error {N n m : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (σ : Spin (N + n)) (τ : Spin N)
    {δ : ℝ}
    (herr : ∀ a, |projectedOverlap U (I a) σ σ - projectedOverlap V (J a) τ τ| ≤ δ) :
    |(rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ - t * rotatedEnergy eig U σ) -
      (rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V τ - t * rotatedEnergy eig₀ V τ)| ≤
      2 * m * |(N + n) * perturbationScale (N + n) - N * perturbationScale N| +
        2 * m * (N * perturbationScale N) * δ := by
  rw [rotatedEnergy_diagonalPerturbation (by omega : 0 < N + n),
    rotatedEnergy_diagonalPerturbation hN, add_sub_cancel_left, add_sub_cancel_left]
  let P := ∑ a, v a * projectedOverlap U (I a) σ σ
  let Q := ∑ a, v a * projectedOverlap V (J a) τ τ
  have hP : |P| ≤ 2 * m := cavity_weighted_overlap_sum_abs v _ hv
    (fun a => projectedOverlap_abs_le_one U (I a) σ σ)
  have hPQ : |P - Q| ≤ 2 * m * δ := cavity_weighted_overlap_sum_difference v _ _ hv herr
  have ha : 0 ≤ (N : ℝ) * perturbationScale N := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ = |(((N + n) * perturbationScale (N + n) - N * perturbationScale N) * P) +
        (N * perturbationScale N) * (P - Q)| := by congr 1; dsimp [P, Q]; push_cast; ring
    _ ≤ |((N + n) * perturbationScale (N + n) - N * perturbationScale N) * P| +
        |(N * perturbationScale N) * (P - Q)| := abs_add_le _ _
    _ ≤ |(N + n) * perturbationScale (N + n) - N * perturbationScale N| * (2 * m) +
        (N * perturbationScale N) * (2 * m * δ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ ha)
    _ = _ := by ring

def cavityDeterministicRate (n m : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  2 * m * (|(N + n) * perturbationScale (N + n) - N * perturbationScale N| +
    C * perturbationScale N)

lemma cavityDeterministicRate_tendsto (n m : ℕ) (C : ℝ) :
    Tendsto (cavityDeterministicRate n m C) atTop (𝓝 0) := by
  have he : Tendsto perturbationScale atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 / 16 : ℝ)) atTop (𝓝 0)
    simpa only [neg_div] using tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 16)
  have hh := ((cavity_deterministic_amplitude_increment_tendsto n).abs.add (he.const_mul C)).const_mul
    (2 * (m : ℝ))
  change Tendsto (fun N => 2 * (m : ℝ) *
    (|(N + n) * perturbationScale (N + n) - N * perturbationScale N| + C * perturbationScale N))
      atTop (𝓝 0)
  simpa only [abs_zero, mul_zero, add_zero] using hh

end InvariantIsing

end

end OAI
