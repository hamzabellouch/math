import OAI.Probability.InvariantIsing.Cavity.CavityLogMeanBound
import OAI.Probability.InvariantIsing.Cavity.CavityRotationMeasurability
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! The actual finite-volume expected logarithmic partition function is
measurable and integrable in the orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityRotationLogMean {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (V : Orthogonal N) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z x)
    ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    ∂gaussianCoordinates

lemma measurable_cavityRotationLogMean {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (cavityRotationLogMean T eig I u) :=
  (measurable_cavityRotationHamiltonian eig I u).exp.stronglyMeasurable
    |>.integral_prod_right' |>.measurable.log.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

lemma cavityRotationLogMean_bound {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (V : Orthogonal N) :
    |cavityRotationLogMean T eig I u V| ≤
      1+2*((∑ i, |eig i|)*N/2)^2+8*Real.exp (2*(4*(N*perturbationScale N^2))) := by
  apply cavity_bounded_base_log_mean_bound
  · intro x
    exact abs_rotatedEnergy_le eig (matrixRotation V⁻¹) (∑ i, |eig i|)
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i)) x.1
  · exact cavityPerturbationCoefficients_sq_le (matrixRotation V⁻¹) I u hu

lemma integrable_cavityRotationLogMean {N m depth : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) :
    Integrable (cavityRotationLogMean T eig I u) μ := by
  apply Integrable.of_bound (measurable_cavityRotationLogMean T eig I u).aestronglyMeasurable
    (1+2*((∑ i, |eig i|)*N/2)^2+8*Real.exp (2*(4*(N*perturbationScale N^2))))
  exact ae_of_all _ fun V => by
    rw [Real.norm_eq_abs]
    exact cavityRotationLogMean_bound T eig I u hu V

end InvariantIsing

end

end OAI
