import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureCGF
import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeIntegrability
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! The actual enriched mean pressure is differentiable in temperature.
Its derivative is the Gibbs interaction energy before temperature scaling. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem hasDerivAt_tensorNamespacedMeanPressure_temperature {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (t : ℝ) :
    HasDerivAt (fun s => tensorNamespacedMeanPressure μ
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h)
      (tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp n b r h (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)) t := by
  let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h
  let Y := fun (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation p.1.1) x.1
  have hY : Measurable (Function.uncurry Y) := measurable_tensorTemperatureObservable eig
  have hB (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) : |Y p x| ≤ K * N / 2 :=
    abs_rotatedEnergy_le eig (specialRotation p.1.1) K hK x.1
  have hd := hasDerivAt_bounded_random_cgf P ν
    (measurable_tensorNamespacedReference _ c I degree amp n r h) Y hY (K * N / 2) hB t
  let M := fun s => tensorNamespacedMeanPressure μ
    (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h
  have he (s : ℝ) : M s = M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := by
    have hi (s : ℝ) := tensorNamespacedLog_integrable μ
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h hh h0
    rw [integral_congr_ae (tensorTemperatureCGF_eq_log_difference hN μ eig c I v degree amp n b r h hh h0 s),
      integral_sub (hi s) (hi 0)]
    dsimp only [M, tensorNamespacedMeanPressure, tensorNamespacedPressure]
    simp only [integral_const_mul]
    ring
  have hf : M = fun s => M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := funext he
  have hfold : (∫ p, ∫ x, Y p x ∂(ν p).tilted (fun x => t * Y p x) ∂P) =
      ∫ p, ∫ x, Y p x ∂tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp n r h p ∂P := by
    apply integral_congr_ae
    filter_upwards [tensorTemperature_reference_fold hN μ eig c I v degree amp n b r h hh h0 t] with p hp
    rw [hp]
  have hhD := (hd.div_const (N : ℝ)).const_add (M 0)
  rw [hfold] at hhD
  rw [← hf] at hhD
  simpa only [M, Y, P, tensorNamespacedObservableAverage, integral_const_mul, integral_mul_const, div_eq_mul_inv,
    mul_comm] using hhD

end InvariantIsing

end

end OAI
