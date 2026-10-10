import OAI.Probability.InvariantIsing.Cavity.CavityActualCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityActualDiagonal

namespace OAI

/-! The actual finite perturbations satisfy the configuration-dependent
cavity error bounds with coefficients tending to zero. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_actual_covariance_rate {N n m depth : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (σ₁ σ₂ : Spin (N + n)) (τ₁ τ₂ : Spin N) (α β : LabeledLeaf depth)
    {C w : ℝ} (hC : 0 ≤ C) (hw : 1 ≤ w)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ -
      projectedOverlap V (J a) τ₁ τ₂| ≤ C / N * w) :
    |cylinderCross (cavityPerturbationCoefficients U I u depth (σ₁, α))
        (cavityPerturbationCoefficients U I u depth (σ₂, β)) -
      cylinderCross (cavityPerturbationCoefficients V J u depth (τ₁, α))
        (cavityPerturbationCoefficients V J u depth (τ₂, β))| ≤
      cavityCovarianceRate n C N * w := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := cavity_actual_covariance_error U V I J u hu σ₁ σ₂ τ₁ τ₂ α β
    (show 0 ≤ C / N * w by positivity) herr
  have he : 4 * ((N : ℝ) * perturbationScale N ^ 2) * (C / N * w) =
      (4 * C * perturbationScale N ^ 2) * w := by field_simp
  rw [he] at h
  refine h.trans ?_
  unfold cavityCovarianceRate
  have ha : 0 ≤ 4 * |((N : ℝ) + n) * perturbationScale (N + n) ^ 2 -
      N * perturbationScale N ^ 2| := by positivity
  have hb : 0 ≤ 4 * (((N : ℝ) + n) * perturbationScale (N + n) ^ 2) *
      (1 / 2 : ℝ) ^ N := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hw ha
  have h₂ := mul_le_mul_of_nonneg_left hw hb
  nlinarith

theorem cavity_actual_diagonal_rate {N n m : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (σ : Spin (N + n)) (τ : Spin N)
    {C w : ℝ} (hw : 1 ≤ w)
    (herr : ∀ a, |projectedOverlap U (I a) σ σ -
      projectedOverlap V (J a) τ τ| ≤ C / N * w) :
    |(rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ - t * rotatedEnergy eig U σ) -
      (rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V τ - t * rotatedEnergy eig₀ V τ)| ≤
      cavityDeterministicRate n m C N * w := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := cavity_diagonal_perturbation_error hN U V I J eig eig₀ v hv t σ τ herr
  have he : 2 * m * ((N : ℝ) * perturbationScale N) * (C / N * w) =
      (2 * m * C * perturbationScale N) * w := by field_simp
  rw [he] at h
  refine h.trans ?_
  unfold cavityDeterministicRate
  have ha : 0 ≤ 2 * (m : ℝ) * |((N : ℝ) + n) * perturbationScale (N + n) -
      N * perturbationScale N| := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hw ha
  nlinarith

lemma cavity_total_error_rate_tendsto (n m : ℕ) (C : ℝ) :
    Tendsto (fun N => cavityDeterministicRate n m C N + 2 * cavityCovarianceRate n C N)
      atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero] using
    (cavityDeterministicRate_tendsto n m C).add ((cavityCovarianceRate_tendsto n C).const_mul 2)

end InvariantIsing

end

end OAI
