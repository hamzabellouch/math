import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeIntegrability
import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeLaw

namespace OAI

/-! The actual field-direction derivative used by the upper contact
argument. All Gaussian insertions and actual model means are identified. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorFieldInsertedLog_cgf_fold {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) (a : ℝ) :
    ∀ᵐ p : TensorFlatDisorder N n × (ℕ → ℝ)
      ∂(((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod gaussianCoordinates),
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p =
        tensorNamespacedLog eig c I degree amp n treeDegree h p.1 +
          cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
            (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a) := by
  let ν := fun p : TensorFlatDisorder N n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd
  have he := random_cgf_insertion_eq hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n treeDegree h)
    (tensorNamespaced_exp_integrable_ae μ eig c I degree amp n b treeDegree h hh h0)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (Real.sqrt a)
  filter_upwards [he] with p hp
  change cgf _ (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a) =
    tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p -
      tensorNamespacedLog eig c I degree amp n treeDegree h p.1 at hp
  linarith

theorem tensorNamespacedMeanPressure_field_insert {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree (fun i => h i + a * g i) =
      tensorFieldInsertionMean μ eig c I degree amp n b treeDegree h g a := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let F := tensorNamespacedLog eig c I degree amp n treeDegree h
  let C := fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
      (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a)
  have hiF : Integrable F Q := tensorNamespacedLog_integrable μ eig c I degree amp n b treeDegree h hh h0
  have hiC : Integrable C (Q.prod gaussianCoordinates) := integrable_random_cylinder_cgf
    (measurable_tensorNamespacedReference eig c I degree amp n treeDegree h)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le) (Real.sqrt a)
  have hmean : (∫ p, tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i) p ∂Q) =
      (∫ p, F p ∂Q) + ∫ p, C p ∂Q.prod gaussianCoordinates := by
    calc
      _ = ∫ p, tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p
          ∂Q.prod gaussianCoordinates :=
        (tensorFieldInsertedLog_identDistrib μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha).integral_eq.symm
      _ = ∫ p, F p.1 + C p ∂Q.prod gaussianCoordinates :=
        integral_congr_ae (tensorFieldInsertedLog_cgf_fold μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a)
      _ = (∫ p, F p.1 ∂Q.prod gaussianCoordinates) + ∫ p, C p ∂Q.prod gaussianCoordinates :=
        integral_add (hiF.comp_fst gaussianCoordinates) hiC
      _ = _ := by rw [integral_fun_fst F, probReal_univ, one_smul]
  unfold tensorFieldInsertionMean tensorNamespacedMeanPressure tensorNamespacedPressure tensorFieldCGFMean
  simp_rw [integral_const_mul]
  rw [hmean]
  change (N : ℝ)⁻¹ * ((∫ p, F p ∂Q) + ∫ p, C p ∂Q.prod gaussianCoordinates) -
      (h n + a * g n) / 2 =
    ((N : ℝ)⁻¹ * (∫ p, F p ∂Q) - h n / 2) +
      (∫ p, C p ∂Q.prod gaussianCoordinates) / N - a * g n / 2
  rw [div_eq_mul_inv (∫ p, C p ∂Q.prod gaussianCoordinates) (N : ℝ)]
  ring

/-- A nonnegative monotone field direction is feasible even when base
increments vanish or tie. The actual centered pressure has the stated
right derivative, with no concentration or path-law input. -/
theorem tensorNamespacedMeanPressure_field_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree (fun i => h i + a * g i))
      (-tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  apply (tensorFieldInsertionMean_right_derivative hN μ eig c I degree amp n b treeDegree h g hg g0).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact tensorNamespacedMeanPressure_field_insert μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha
  · exact tensorNamespacedMeanPressure_field_insert μ eig c I degree amp n b treeDegree h g hh h0 hg g0 0 le_rfl

end InvariantIsing

end

end OAI
