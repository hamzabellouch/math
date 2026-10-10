import OAI.Probability.InvariantIsing.Fields.SpinPriorFieldInsertionLaw
import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadeAverage

namespace OAI

/-! The actual field-direction derivative used by the upper contact
argument. All Gaussian insertions and actual model means are identified. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorFieldInsertedLog_cgf_fold {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) (a : ℝ) :
    ∀ᵐ p : TensorFlatDisorder N n × (ℕ → ℝ)
      ∂(((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod gaussianCoordinates),
      spinPriorFieldInsertedLog π eig c I degree amp n treeDegree h g a p =
        spinPriorNamespacedLog (n := n) π eig c I degree amp treeDegree h p.1 +
          cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
            (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h p.1) (Real.sqrt a) := by
  let ν := fun p : TensorFlatDisorder N n =>
    labeledSpinReference n π p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n π p.1.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n π).comp measurable_fst.snd
  have he := random_cgf_insertion_eq hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n treeDegree h)
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree amp n b treeDegree h hh h0)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (Real.sqrt a)
  filter_upwards [he] with p hp
  change cgf _ (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h p.1) (Real.sqrt a) =
    spinPriorFieldInsertedLog π eig c I degree amp n treeDegree h g a p -
      spinPriorNamespacedLog (n := n) π eig c I degree amp treeDegree h p.1 at hp
  linarith

theorem spinPriorMeanPressure_field_insert {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    spinPriorMeanPressure (n := n) μ π eig c I degree amp b treeDegree (fun i => h i + a * g i) =
      spinPriorFieldInsertionMean μ π eig c I degree amp n b treeDegree h g a := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let F := spinPriorNamespacedLog (n := n) π eig c I degree amp treeDegree h
  let C := fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
      (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h p.1) (Real.sqrt a)
  have hiF : Integrable F Q := spinPriorNamespacedLog_integrable (n := n) μ π eig c I degree amp b treeDegree h hh h0
  have hiC : Integrable C (Q.prod gaussianCoordinates) := integrable_random_cylinder_cgf
    (measurable_spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le) (Real.sqrt a)
  have hmean : (∫ p, spinPriorNamespacedLog (n := n) π eig c I degree amp treeDegree (fun i => h i + a * g i) p ∂Q) =
      (∫ p, F p ∂Q) + ∫ p, C p ∂Q.prod gaussianCoordinates := by
    calc
      _ = ∫ p, spinPriorFieldInsertedLog π eig c I degree amp n treeDegree h g a p
          ∂Q.prod gaussianCoordinates :=
        (spinPriorFieldInsertedLog_identDistrib μ π eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha).integral_eq.symm
      _ = ∫ p, F p.1 + C p ∂Q.prod gaussianCoordinates :=
        integral_congr_ae (spinPriorFieldInsertedLog_cgf_fold μ π eig c I degree amp n b treeDegree h g hh h0 hg g0 a)
      _ = (∫ p, F p.1 ∂Q.prod gaussianCoordinates) + ∫ p, C p ∂Q.prod gaussianCoordinates :=
        integral_add (hiF.comp_fst gaussianCoordinates) hiC
      _ = _ := by rw [integral_fun_fst F, probReal_univ, one_smul]
  unfold spinPriorFieldInsertionMean spinPriorMeanPressure spinPriorFieldCGFMean
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
theorem spinPriorMeanPressure_field_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => spinPriorMeanPressure (n := n) μ π eig c I degree amp b treeDegree (fun i => h i + a * g i))
      (-spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  apply (spinPriorFieldInsertionMean_right_derivative hN μ π eig c I degree amp n b treeDegree h g hg g0).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact spinPriorMeanPressure_field_insert μ π eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha
  · exact spinPriorMeanPressure_field_insert μ π eig c I degree amp n b treeDegree h g hh h0 hg g0 0 le_rfl

end InvariantIsing

end

end OAI
