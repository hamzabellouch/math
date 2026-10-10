import OAI.Probability.InvariantIsing.Arrays.TensorZeroAmplitude
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationBaseComparison
import OAI.Probability.InvariantIsing.Arrays.TensorContactContinuity

namespace OAI

/-! With both the linear-field heights and the monomial amplitudes zero,
the cascade leaves the original finite Ising pressure unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma vectorGaussianLaw_zero_ae (N : ℕ) :
    ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z = 0 := by
  have hi (i : Fin N) :
      ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z i = 0 := by
    have hz : ∀ᵐ x ∂gaussianReal 0 0, x = 0 := by
      simp [gaussianReal_zero_var, ae_dirac_eq]
    exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 0) i).quasiMeasurePreserving.ae hz
  filter_upwards [ae_all_iff.mpr hi] with z hz
  funext i
  exact hz i

lemma integral_vectorGaussianLaw_zero {N : ℕ} (F : (Fin N → ℝ) → ℝ) :
    (∫ z, F z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ))) = F 0 := by
  calc
    _ = ∫ _ : Fin N → ℝ, F 0 ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [vectorGaussianLaw_zero_ae N] with z hz
      rw [hz]
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

lemma logMean_vectorGaussianLaw_zero {N : ℕ} {b : ℝ} (hb : b ≠ 0)
    (F : (Fin N → ℝ) → ℝ) :
    logMean b (vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) F = F 0 := by
  unfold logMean
  rw [integral_vectorGaussianLaw_zero, Real.log_exp]
  exact mul_div_cancel_left₀ (F 0) hb

lemma rotatedCascadeValue_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) :
    rotatedCascadeValue n b (fun _ => 0) eig U c z = rotatedFieldTerminal eig U c z := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change logMean (b 0) (vectorGaussianLaw N 0 : Measure (Fin N → ℝ))
      (fun w => rotatedCascadeValue n (fun i => b (i + 1)) (fun _ => 0) eig U c (z + w)) = _
    rw [logMean_vectorGaussianLaw_zero (hb.1 0 (by omega)).1.ne']
    simpa only [add_zero] using ih (fun i => b (i + 1)) hb.tail

lemma rotatedEnrichedPressure_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b (fun _ => 0) 0 eig U c = rotatedPressure eig U c := by
  unfold rotatedEnrichedPressure
  rw [integral_vectorGaussianLaw_zero, rotatedCascadeValue_zero_variance n b hb]
  simp only [rotatedPressure, rotatedFieldTerminal, add_zero]

lemma varianceIncrement_zero_path (i : ℕ) : varianceIncrement (fun _ => 0) i = 0 := by
  cases i <;> simp [varianceIncrement, pathIncrement]

/-- The exact unperturbed pressure at zero field height, including the root. -/
theorem tensorPathPressure_zero_field {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (r : Fin k → ℕ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n r (fun _ => 0) (i + 1))
      (tensorPathProfile I degree n r (fun _ => 0) 0) = rotatedPressure eig U c := by
  rw [tensorPathPressure_zero_amplitude]
  simp_rw [varianceIncrement_zero_path]
  exact rotatedEnrichedPressure_zero_variance n b hb eig U c

/-- At zero random-field height the centered actual pressure differs from
the ordinary Haar-mean pressure only by the established perturbation cost. -/
theorem tensorNamespacedMeanPressure_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) (fun _ => 0) -
      ∫ U : SpecialOrthogonal N, rotatedPressure (fun i => t * eig i) (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  have h := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ eig c I
    u hu v hv t n b (fun _ => 0) hb monotone_const (by rfl)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) 0) =
      rotatedPressure (fun i => t * eig i) (specialRotation U) c := by
    exact tensorPathPressure_zero_field (fun i => t * eig i) (specialRotation U) c I
      (fun j : Fin N => enumeratedSpectralDegree m j) n b hb (fun j => enumeratedTreeDegree m j)
  simp_rw [hbase] at h
  simpa only [zero_div, sub_zero] using h

theorem tensorContactPressure_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorContactPressure μ eig c I b (t, (fun _ : Fin (n + 1) => 0), u, v) -
      ∫ U : SpecialOrthogonal N, rotatedPressure (fun i => t * eig i) (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  have hzero : finiteFieldPath (fun _ : Fin (n + 1) => (0 : ℝ)) = fun _ => 0 := by
    funext i
    simp only [finiteFieldPath, ite_self, Finset.sum_const_zero]
  simpa only [tensorContactPressure, hzero] using
    tensorNamespacedMeanPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I u hu v hv t n b hb

theorem tensorContactPressure_one_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorContactPressure μ eig c I b (1, (fun _ : Fin (n + 1) => 0), u, v) -
      ∫ U : SpecialOrthogonal N, rotatedPressure eig (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  simpa only [one_mul] using
    tensorContactPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I u hu v hv 1 n b hb

end InvariantIsing

end

end OAI
