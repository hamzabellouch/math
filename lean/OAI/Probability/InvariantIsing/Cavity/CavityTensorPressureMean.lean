import OAI.Probability.InvariantIsing.Cavity.CavityTensorLogLaw
import OAI.Probability.InvariantIsing.Cavity.CavityTreeLogMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityBasePerturbedLaw
import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureModulus

namespace OAI

/-! The literal physical Haar/tree logarithmic mean equals dimension times
the pressure used to choose the perturbation minima. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_oriented_tensor_log_mean {N m depth : ℕ} (hN : 0<N)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    cavityRotationLogMean T eig I u V =
      ∫ z, tensorNamespacedLog eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
        ((cavityOrientationLift hN V⁻¹,T),z) ∂gaussianCoordinates := by
  have he := (cavity_orientation_log_mean hN V⁻¹ T eig I u).symm.trans
    (cavity_rotation_tensor_log_mean (cavityOrientationLift hN V⁻¹) T eig I u)
  simpa only [inv_inv] using he

theorem cavity_tensor_pressure_mean {N m depth : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents depth b) :
    (∫ p, cavityRotationLogMean p.2 (diagonalPerturbedEigenvalues eig I v t) I u p.1
      ∂μ.prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) =
      (N : ℝ)*tensorPerturbationPressureMean (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I
        (fun j => u j) v t depth b (fun _ => 0) := by
  let ν := cavityOrientedBaseLaw hN μ
  let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j : Fin N => u j)
  let eig' := diagonalPerturbedEigenvalues eig I v t
  let F := tensorNamespacedLog eig' (fun _ => 0) I degree amp depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  let G := fun p : SpecialOrthogonal N × LabeledTree depth => ∫ z, F (p,z) ∂gaussianCoordinates
  have hFm : Measurable F := measurable_tensorNamespacedLog eig' (fun _ => 0) I degree amp depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  have hG : Measurable G := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hFi : Integrable F ((ν.prod θ).prod gaussianCoordinates) :=
    tensorNamespacedLog_integrable ν eig' (fun _ => 0) I degree amp depth b
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) monotone_const le_rfl
  have hmap := (cavityOrientedBaseLaw_preserving hN μ).prod (MeasurePreserving.id θ)
  have hE : (∫ p, cavityRotationLogMean p.2 eig' I u p.1 ∂μ.prod θ) = ∫ p, G p ∂ν.prod θ := by
    calc
      _ = ∫ p, G (cavityOrientationLift hN p.1⁻¹,p.2) ∂μ.prod θ := by
        apply integral_congr_ae
        exact ae_of_all _ fun p => cavity_oriented_tensor_log_mean hN p.1 p.2 eig' I u
      _ = _ := hmap.hasLaw.integral_comp hG.aestronglyMeasurable
  have hP := tensorNamespacedMeanPressure_eq_perturbation ν eig (fun _ => 0) I
    (fun j => u j) v t depth b (fun _ => 0) hb
  simp only [zero_div, sub_zero] at hP
  rw [← hP]
  change (∫ p, cavityRotationLogMean p.2 eig' I u p.1 ∂μ.prod θ) =
    (N : ℝ)*((∫ p, (N : ℝ)⁻¹*F p ∂(ν.prod θ).prod gaussianCoordinates) - 0/2)
  rw [hE, zero_div, sub_zero, integral_const_mul, integral_prod _ hFi]
  change (∫ p, G p ∂ν.prod θ) = (N : ℝ)*((N : ℝ)⁻¹*∫ p, G p ∂ν.prod θ)
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

end InvariantIsing

end

end OAI
