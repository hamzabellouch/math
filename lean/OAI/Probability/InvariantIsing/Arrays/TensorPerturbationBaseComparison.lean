import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureModulus
import OAI.Probability.InvariantIsing.Arrays.TensorObjectiveContinuity

namespace OAI

/-! The full finite perturbation comparison after averaging over the actual
Haar and Gaussian disorder. The bound is uniform in the field heights. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorNamespacedMeanPressure_perturbation_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N) (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (hμ : μ.IsMulLeftInvariant) (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (t : ℝ) (n : ℕ) (b h : ℕ → ℝ) (hb : CascadeExponents n b)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) h -
      ((∫ U : SpecialOrthogonal N,
        tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
          (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
          (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
            n (fun j => enumeratedTreeDegree m j) h (i + 1))
          (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
            n (fun j => enumeratedTreeDegree m j) h 0) ∂μ) - h n / 2)| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let r := fun j : Fin N => enumeratedTreeDegree m j
  let profile := tensorPathProfile I degree n r h
  let A := fun U : SpecialOrthogonal N =>
    tensorEnrichedPressure (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) c I
      degree (tensorPerturbationAmplitude N u) n b (fun i => profile (i + 1)) (profile 0)
  let B := fun U : SpecialOrthogonal N =>
    tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
      degree 0 n b (fun i => profile (i + 1)) (profile 0)
  have hA := tensorPathPressure_haar_mean hhaar hgauss hN μ hμ
    (diagonalPerturbedEigenvalues eig I v t) c I degree (tensorPerturbationAmplitude N u) n r b hb h
  have hB := tensorPathPressure_haar_mean hhaar hgauss hN μ hμ
    (fun i => t * eig i) c I degree 0 n r b hb h
  rw [tensorNamespacedMeanPressure_eq_disorder μ _ c I degree _ n b r h hb, hA.2,
    sub_sub_sub_cancel_right]
  change |(∫ U, A U ∂μ) - ∫ U, B U ∂μ| ≤ _
  rw [← integral_sub hA.1 hB.1]
  have hbound (U : SpecialOrthogonal N) :
      |A U - B U| ≤ 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 :=
    fullPerturbationPressure_cost (by omega) eig c (specialRotation U) I degree u hu v hv
      t n r b hb h hh h0
  have hbnd : ∀ᵐ U ∂μ, ‖A U - B U‖ ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 :=
    ae_of_all μ (fun U => by simpa only [Real.norm_eq_abs] using hbound U)
  have hi := norm_integral_le_of_norm_le_const hbnd
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi

end InvariantIsing

end

end OAI
