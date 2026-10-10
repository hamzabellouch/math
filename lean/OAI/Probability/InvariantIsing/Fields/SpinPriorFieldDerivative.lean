import OAI.Probability.InvariantIsing.Fields.SpinPriorReplicaAverage
import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadePressure
import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivative
import OAI.Probability.IsingPerceptron.VarianceDerivative

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
actual namespaced tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorFieldCGFMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : TensorFlatDisorder N n × (ℕ → ℝ),
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) z.2)
      (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h z.1) (Real.sqrt a)
    ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod
      gaussianCoordinates

def spinPriorFieldInsertionMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  spinPriorMeanPressure (n := n) μ π eig c I degree amp b treeDegree h +
    spinPriorFieldCGFMean μ π eig c I degree amp n b treeDegree h g a / N - a * g n / 2

theorem spinPriorFieldCGFMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (spinPriorFieldCGFMean μ π eig c I degree amp n b treeDegree h g)
      ((N * g n - N * spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g)) / 2) (Ici 0) 0 := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h
  have hν : Measurable ν := measurable_spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h
  have hd := hasDerivWithinAt_random_cylinder_variance (P := Q) hν
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (d := N * g n) (fun x => by rw [cylinderCross_self, tensorLinearCoefficients_variance n g hg g0])
    (v := 0) (by norm_num)
  have hc : (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
      cylinderCross (tensorLinearCoefficients n g (σ 1)) (tensorLinearCoefficients n g (σ 0))) =
      (fun σ => N * tensorFieldPairObservable g σ) :=
    funext (tensorLinearCoefficients_cross_normalized hN n g hg g0)
  rw [Real.sqrt_zero, hc, randomReplicaAverage_zero_reference] at hd
  simp only [referenceReplicaMean_const_mul, integral_const_mul] at hd
  exact hd

/-- The diagonal Gaussian term is canceled by the actual `-h(top)/2`
normalization. This is the contact derivative, including zero and tied
field increments, before identifying the inserted field with `h+a*g`. -/
theorem spinPriorFieldInsertionMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (spinPriorFieldInsertionMean μ π eig c I degree amp n b treeDegree h g)
      (-spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  have hd := spinPriorFieldCGFMean_right_derivative hN μ π eig c I degree amp n b treeDegree h g hg g0
  have hm := ((hd.div_const (N : ℝ)).const_add
    (spinPriorMeanPressure (n := n) μ π eig c I degree amp b treeDegree h)).fun_sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (g n)).div_const 2).hasDerivWithinAt
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N * g n - N * spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
      (fun _ => tensorFieldPairObservable g)) / 2 / N - 1 * g n / 2 =
      -spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2 := by
    field_simp
    ring
  rw [he] at hm
  convert hm using 1
  rfl


end InvariantIsing

end

end OAI
