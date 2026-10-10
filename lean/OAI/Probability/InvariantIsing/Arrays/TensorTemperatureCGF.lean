import OAI.Probability.InvariantIsing.Pressure.RandomBoundedDerivative
import OAI.Probability.InvariantIsing.Arrays.TensorObservableAverageLaw

namespace OAI

/-! Temperature is a bounded deterministic tilt of the actual enriched
Gibbs reference, with all Gaussian and cascade variables retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma tensorTemperatureHamiltonian_affine {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) (t : ℝ) :
    tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p =
      fun x => tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0)
        c I degree amp n r h p x + t * rotatedEnergy eig (specialRotation p.1.1) x.1 := by
  funext x
  unfold tensorNamespacedHamiltonian
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN]
  ring

lemma measurable_tensorTemperatureObservable {N n : ℕ} (eig : Fin N → ℝ) :
    Measurable (fun p : TensorFlatDisorder N n × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1.1) p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  unfold rotatedEnergy
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_specialRotation_eval (spinVector x.1) i).comp measurable_fst.fst).pow_const 2
      |>.const_mul (eig i)).const_mul _

lemma tensorTemperature_reference_fold {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p).tilted
        (fun x => t * rotatedEnergy eig (specialRotation p.1.1) x.1) =
      tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p := by
  filter_upwards [tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let G := fun x : Spin N × LabeledLeaf n => t * rotatedEnergy eig (specialRotation p.1.1) x.1
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change (gibbsProbability ν H).tilted G = gibbsProbability ν _
  rw [he, gibbsProbability_eq_tilted ν H hH,
    gibbsProbability_eq_tilted ν (fun x => H x + G x) hi, tilted_tilted hH G]
  rfl

lemma tensorTemperatureCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1)
        (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p) t =
      tensorNamespacedLog (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p -
        tensorNamespacedLog (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p := by
  filter_upwards [tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
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
