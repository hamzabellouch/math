import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFlatMean
import OAI.Probability.InvariantIsing.Arrays.TensorGaussianMean
import OAI.Probability.InvariantIsing.Arrays.TensorProfiles

namespace OAI

/-! Rotation comparison for the actual disorder-averaged tensor cascade pressure. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_tensorEnrichedPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (root : SpinTensorIndex I degree → ℝ≥0) :
    Measurable (fun U : SpecialOrthogonal N =>
      tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b v root) :=
  (measurable_tensorCascadeValue_joint eig c I degree amplitude n b v).stronglyMeasurable.integral_prod_right.measurable.const_mul (N : ℝ)⁻¹

/-- Gaussian covariance comparison transfers through the exact flat-model
mean identity to the backward recursion pressure itself. -/
theorem abs_tensorEnrichedPressure_sub_rotation_le {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (site : ℕ → ℝ≥0) (monomial : ℕ → Fin k → ℝ≥0) :
    let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
    |tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig (specialRotation V) c I degree amplitude n b (fun i => v (i + 1)) (v 0)| ≤
      (K + 2 * (N : ℝ)⁻¹ * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ))) * frobeniusDistance U V := by
  intro v
  let F := fun R T => ∫ g : ℕ → ℝ,
    tensorFlatLog eig (specialRotation R) c I degree amplitude n v (T, g) ∂gaussianCoordinates
  have hi (R : SpecialOrthogonal N) : Integrable (F R)
      (labeledCascadeLaw n b : Measure (LabeledTree n)) :=
    (tensorFlatLog_integrable eig (specialRotation R) c I degree amplitude n b v).integral_prod_left
  let L := K * N + 2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
    ∑ a, (degree j a : ℝ))
  have hbound (T : LabeledTree n) : |F U T - F V T| ≤ L * frobeniusDistance U V := by
    exact tensorLeafLogMean_abs_sub_le hN eig c U V K hK heig I degree amplitude n
      (fun i => site i) (fun i => monomial i)
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
  have hm : |(∫ T, F U T ∂(labeledCascadeLaw n b : Measure (LabeledTree n))) -
      ∫ T, F V T ∂(labeledCascadeLaw n b : Measure (LabeledTree n))| ≤ L * frobeniusDistance U V := by
    rw [← integral_sub (hi U) (hi V), ← Real.norm_eq_abs]
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
        (C := L * frobeniusDistance U V) (ae_of_all _ fun T => by
          simpa only [Real.norm_eq_abs] using hbound T)
  rw [tensorEnrichedPressure_eq_flat_mean hN eig (specialRotation U) c I degree amplitude n b v hb,
    tensorEnrichedPressure_eq_flat_mean hN eig (specialRotation V) c I degree amplitude n b v hb,
    ← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg _))]
  refine (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq ?_
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  dsimp only [L]
  field_simp

/-- For the manuscript's tree power increments, the rotation modulus
depends on the perturbation amplitudes and degrees, not the cascade depth. -/
theorem abs_tensorPathPressure_sub_rotation_le {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    let v := tensorPathProfile I degree n treeDegree h
    |tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig (specialRotation V) c I degree amplitude n b (fun i => v (i + 1)) (v 0)| ≤
      (K + 2 * (N : ℝ)⁻¹ * (∑ j, amplitude j ^ 2 * ∑ a, (degree j a : ℝ))) * frobeniusDistance U V := by
  intro v
  have hc := abs_tensorEnrichedPressure_sub_rotation_le hN eig c U V K hK heig I degree amplitude n b hb
    (varianceIncrement h) (fun i j => varianceIncrement (monomialPath n (treeDegree j)) i)
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ (show 0 ≤ frobeniusDistance U V from Real.sqrt_nonneg _)
  have hc := mul_le_mul_of_nonneg_left
    (tensorPathProfile_rotation_cap degree amplitude n treeDegree)
    (show 0 ≤ 2 * (N : ℝ)⁻¹ by positivity)
  linarith

end InvariantIsing

end

end OAI
