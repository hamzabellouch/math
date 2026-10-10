import OAI.Probability.InvariantIsing.Core.MixedSpectralFeatures
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorCascade

namespace OAI

/-! Rotation continuity of the concrete finite tensor perturbation marks. -/

noncomputable section

open scoped BigOperators NNReal

namespace InvariantIsing

lemma spinTensorFeature_increment_covariance {N m k : ℕ}
    (U V W : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      (spinTensorFeature U I degree amplitude σ i - spinTensorFeature V I degree amplitude σ i) *
        spinTensorFeature W I degree amplitude τ i) =
      ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
        ∑ v : SpectralTensorIndex I (degree j),
          (spectralMonomialFeature U I (degree j) σ v -
            spectralMonomialFeature V I (degree j) σ v) *
              spectralMonomialFeature W I (degree j) τ v := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature, sub_self, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Linear spin-field marks cancel in the rotation increment. Only the
finite spectral tensor covariance contributes to the rotation modulus. -/
theorem spinTensorFeature_increment_covariance_le {N m k : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    |∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      (spinTensorFeature (specialRotation U) I degree amplitude σ i -
        spinTensorFeature (specialRotation V) I degree amplitude σ i) *
          spinTensorFeature (specialRotation W) I degree amplitude τ i| ≤
      (∑ j, (monomial j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ)) *
        frobeniusDistance U V := by
  rw [spinTensorFeature_increment_covariance]
  calc
    _ ≤ ∑ j, |(monomial j : ℝ) * amplitude j ^ 2 *
        ∑ v : SpectralTensorIndex I (degree j),
          (spectralMonomialFeature (specialRotation U) I (degree j) σ v -
            spectralMonomialFeature (specialRotation V) I (degree j) σ v) *
              spectralMonomialFeature (specialRotation W) I (degree j) τ v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
        ((∑ a, (degree j a : ℝ)) * frobeniusDistance U V) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (spectralMonomialFeature_increment_cross_le hN U V W I (degree j) σ τ)
        (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end InvariantIsing

end

end OAI
