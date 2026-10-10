import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage
import OAI.Probability.IsingPerceptron.VarianceDerivative

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma randomReplicaAverage_zero_reference {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (A : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    randomReplicaAverage P ν A 0 D =
      ∫ ω, referenceReplicaMean (ν ω) (fun _ => 0) D ∂P := by
  unfold randomReplicaAverage
  simp only [zero_mul]
  rw [integral_fun_fst (fun ω => referenceReplicaMean (ν ω) (fun _ => 0) D)]
  simp only [probReal_univ, one_smul]

def tensorNamespacedMeanPressure {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (∫ p, tensorNamespacedPressure eig c I degree amp n treeDegree h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) - h n / 2

def tensorFieldCGFMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : TensorFlatDisorder N n × (ℕ → ℝ),
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) z.2)
      (tensorNamespacedReference eig c I degree amp n treeDegree h z.1) (Real.sqrt a)
    ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod
      gaussianCoordinates

def tensorFieldInsertionMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree h +
    tensorFieldCGFMean μ eig c I degree amp n b treeDegree h g a / N - a * g n / 2

def tensorFieldPairObservable {N n : ℕ} (g : ℕ → ℝ)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : ℝ :=
  ((N : ℝ)⁻¹ * ∑ i, spinValue ((σ 1).1 i) * spinValue ((σ 0).1 i)) *
    g (labeledCommonDepth n (σ 1).2 (σ 0).2)

lemma tensorLinearCoefficients_cross {N : ℕ} (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLinearCoefficients n g x) (tensorLinearCoefficients n g y) =
      g (labeledCommonDepth n x.2 y.2) * ∑ i, spinValue (x.1 i) * spinValue (y.1 i) :=
  treeField_path_cross n x.2 y.2 hg g0 _ _

lemma tensorLinearCoefficients_variance {N : ℕ} (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) (x : Spin N × LabeledLeaf n) :
    (tensorLinearCoefficients n g x).sum (fun _ c => c ^ 2) = N * g n := by
  rw [← cylinderCross_self, tensorLinearCoefficients_cross n g hg g0, labeledCommonDepth_self]
  simp only [← pow_two, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- The Gaussian covariance derivative is exactly the actual spin
overlap times the field direction at the common ancestor level. -/
lemma tensorLinearCoefficients_cross_normalized {N : ℕ} (hN : 0 < N) (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (σ : Fin 2 → Spin N × LabeledLeaf n) :
    cylinderCross (tensorLinearCoefficients n g (σ 1))
      (tensorLinearCoefficients n g (σ 0)) = N * tensorFieldPairObservable g σ := by
  rw [tensorLinearCoefficients_cross n g hg g0]
  unfold tensorFieldPairObservable
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem tensorFieldCGFMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (tensorFieldCGFMean μ eig c I degree amp n b treeDegree h g)
      ((N * g n - N * tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g)) / 2) (Ici 0) 0 := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := tensorNamespacedReference eig c I degree amp n treeDegree h
  have hν : Measurable ν := measurable_tensorNamespacedReference eig c I degree amp n treeDegree h
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
theorem tensorFieldInsertionMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (tensorFieldInsertionMean μ eig c I degree amp n b treeDegree h g)
      (-tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  have hd := tensorFieldCGFMean_right_derivative hN μ eig c I degree amp n b treeDegree h g hg g0
  have hm := ((hd.div_const (N : ℝ)).const_add
    (tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree h)).fun_sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (g n)).div_const 2).hasDerivWithinAt
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N * g n - N * tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
      (fun _ => tensorFieldPairObservable g)) / 2 / N - 1 * g n / 2 =
      -tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2 := by
    field_simp
    ring
  rw [he] at hm
  convert hm using 1
  rfl


end InvariantIsing

end

end OAI
