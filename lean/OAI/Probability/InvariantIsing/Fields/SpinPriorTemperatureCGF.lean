import OAI.Probability.InvariantIsing.Fields.SpinPriorExponential
import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureCGF

namespace OAI

/-! Temperature is a bounded tilt with the actual quenched cascade and
constrained spin prior retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology
namespace InvariantIsing

lemma spinPriorTemperature_reference_fold {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p).tilted
        (fun x => t * rotatedEnergy eig (specialRotation p.1.1) x.1) =
      spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h p := by
  filter_upwards [spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let G := fun x : Spin N × LabeledLeaf n => t * rotatedEnergy eig (specialRotation p.1.1) x.1
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change (gibbsProbability ν H).tilted G = gibbsProbability ν
    (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p)
  rw [he, gibbsProbability_eq_tilted ν H hH,
    gibbsProbability_eq_tilted ν (fun x => H x + G x) hi, tilted_tilted hH G]
  rfl

lemma spinPriorTemperatureCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1)
        (spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p) t =
      spinPriorNamespacedLog π (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h p -
        spinPriorNamespacedLog π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p := by
  filter_upwards [spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let Y := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + t * Y x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hH hi]
  rw [show (fun x => H x + t * Y x) = tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p from he.symm]
  rfl

end InvariantIsing

end

end OAI
