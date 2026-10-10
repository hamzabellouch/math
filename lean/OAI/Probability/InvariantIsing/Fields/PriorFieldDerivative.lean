import OAI.Probability.InvariantIsing.Fields.PriorFieldInsertionLaw
import OAI.Probability.InvariantIsing.Fields.PriorReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeIntegrability

namespace OAI

/-! The right field derivative of the actual centered constrained-prior
pressure, allowing zero and repeated field-variance levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def priorNamespacedMeanPressure {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (N : ℝ)⁻¹*(∫ p, priorNamespacedLog ν eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates)-h n/2

def priorFieldCGFMean {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∫ p : (SpecialOrthogonal N × (ℕ → ℝ)) × (ℕ → ℝ),
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
      (priorNamespacedReference ν eig c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p.1) (Real.sqrt a)
    ∂(μ.prod gaussianCoordinates).prod gaussianCoordinates

def priorFieldInsertionMean {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  priorNamespacedMeanPressure μ ν eig c I degree amp r h+
    priorFieldCGFMean μ ν eig c I degree amp r h g a/N-a*g n/2

lemma priorFieldCGFMean_right_derivative {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (priorFieldCGFMean μ ν eig c I degree amp r h g)
      ((N*g n-N*priorNamespacedReplicaAverage μ ν eig c I degree amp r h
        (fun _ => tensorFieldPairObservable g))/2) (Ici 0) 0 := by
  let Q := μ.prod gaussianCoordinates
  let G := priorNamespacedReference ν eig c I degree amp (fun i => tensorPathProfile I degree n r h i)
  have hd := hasDerivWithinAt_random_cylinder_variance (P := Q) (ν := G)
    (measurable_priorNamespacedReference ν eig c I degree amp
      (fun i => tensorPathProfile I degree n r h i))
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (d := N*g n) (fun x => by rw [cylinderCross_self,tensorLinearCoefficients_variance n g hg g0])
    (v := 0) (by norm_num)
  have hc : (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
      cylinderCross (tensorLinearCoefficients n g (σ 1)) (tensorLinearCoefficients n g (σ 0))) =
      (fun σ => N*tensorFieldPairObservable g σ) :=
    funext (tensorLinearCoefficients_cross_normalized hN n g hg g0)
  rw [Real.sqrt_zero,hc,randomReplicaAverage_zero_reference] at hd
  simp only [referenceReplicaMean_const_mul,integral_const_mul] at hd
  exact hd

lemma priorFieldInsertionMean_right_derivative {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (priorFieldInsertionMean μ ν eig c I degree amp r h g)
      (-priorNamespacedReplicaAverage μ ν eig c I degree amp r h
        (fun _ => tensorFieldPairObservable g)/2) (Ici 0) 0 := by
  have hd := priorFieldCGFMean_right_derivative hN μ ν eig c I degree amp r h g hg g0
  have hm := ((hd.div_const (N : ℝ)).const_add
    (priorNamespacedMeanPressure μ ν eig c I degree amp r h)).fun_sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (g n)).div_const 2).hasDerivWithinAt
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (N*g n-N*priorNamespacedReplicaAverage μ ν eig c I degree amp r h
      (fun _ => tensorFieldPairObservable g))/2/N-1*g n/2 =
      -priorNamespacedReplicaAverage μ ν eig c I degree amp r h
        (fun _ => tensorFieldPairObservable g)/2 := by
    field_simp
    ring
  rw [he] at hm
  exact hm

lemma priorFieldInsertedLog_cgf_fold {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (hg : Monotone g) (g0 : 0 ≤ g 0) (a : ℝ) :
    ∀ᵐ p ∂(μ.prod gaussianCoordinates).prod gaussianCoordinates,
      priorFieldInsertedLog ν eig c I degree amp r h g a p =
        priorNamespacedLog ν eig c I degree amp (fun i => tensorPathProfile I degree n r h i) p.1+
        cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
          (priorNamespacedReference ν eig c I degree amp
            (fun i => tensorPathProfile I degree n r h i) p.1) (Real.sqrt a) := by
  have he := random_cgf_insertion_eq (ν := fun _ : SpecialOrthogonal N × (ℕ → ℝ) => ν)
    measurable_const (measurable_priorNamespacedHamiltonian eig c I degree amp _)
    (priorNamespaced_exp_integrable_ae μ ν eig c I degree amp r h hh h0)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (Real.sqrt a)
  filter_upwards [he] with p hp
  change cgf _ (priorNamespacedReference ν eig c I degree amp _ p.1) (Real.sqrt a) =
    priorFieldInsertedLog ν eig c I degree amp r h g a p-
      priorNamespacedLog ν eig c I degree amp _ p.1 at hp
  linarith

theorem priorNamespacedMeanPressure_field_insert
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (hg : Monotone g) (g0 : 0 ≤ g 0) (a : ℝ) (ha : 0 ≤ a) :
    priorNamespacedMeanPressure μ ν eig c I degree amp r (fun i => h i+a*g i) =
      priorFieldInsertionMean μ ν eig c I degree amp r h g a := by
  let Q := μ.prod gaussianCoordinates
  let F := priorNamespacedLog ν eig c I degree amp (fun i => tensorPathProfile I degree n r h i)
  let C := fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × (ℕ → ℝ) =>
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
      (priorNamespacedReference ν eig c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p.1) (Real.sqrt a)
  have hiF : Integrable F Q := priorNamespacedLog_integrable hhaar hgauss hN μ hμ ν eig c I
    degree amp (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hiC : Integrable C (Q.prod gaussianCoordinates) := integrable_random_cylinder_cgf
    (measurable_priorNamespacedReference ν eig c I degree amp _)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le) (Real.sqrt a)
  have hmean : (∫ p, priorNamespacedLog ν eig c I degree amp
      (fun j => tensorPathProfile I degree n r (fun i => h i+a*g i) j) p ∂Q) =
      (∫ p, F p ∂Q)+∫ p, C p ∂Q.prod gaussianCoordinates := by
    calc
      _ = ∫ p, priorFieldInsertedLog ν eig c I degree amp r h g a p ∂Q.prod gaussianCoordinates :=
        (priorFieldInsertedLog_identDistrib μ ν eig c I degree amp r h g hh h0 hg g0 a ha).integral_eq.symm
      _ = ∫ p, F p.1+C p ∂Q.prod gaussianCoordinates :=
        integral_congr_ae (priorFieldInsertedLog_cgf_fold μ ν eig c I degree amp r h g hh h0 hg g0 a)
      _ = (∫ p, F p.1 ∂Q.prod gaussianCoordinates)+∫ p, C p ∂Q.prod gaussianCoordinates :=
        integral_add (hiF.comp_fst gaussianCoordinates) hiC
      _ = _ := by rw [integral_fun_fst F,probReal_univ,one_smul]
  unfold priorNamespacedMeanPressure priorFieldInsertionMean priorFieldCGFMean
  rw [hmean]
  change (N : ℝ)⁻¹*((∫ p, F p ∂Q)+∫ p, C p ∂Q.prod gaussianCoordinates)-(h n+a*g n)/2 =
    ((N : ℝ)⁻¹*(∫ p, F p ∂Q)-h n/2)+(∫ p, C p ∂Q.prod gaussianCoordinates)/N-a*g n/2
  ring

theorem priorNamespacedMeanPressure_field_right_derivative
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ)
    (h g : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => priorNamespacedMeanPressure μ ν eig c I degree amp r (fun i => h i+a*g i))
      (-priorNamespacedReplicaAverage μ ν eig c I degree amp r h
        (fun _ => tensorFieldPairObservable g)/2) (Ici 0) 0 := by
  apply (priorFieldInsertionMean_right_derivative (by omega) μ ν eig c I degree amp r h g hg g0).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact priorNamespacedMeanPressure_field_insert hhaar hgauss hN μ hμ ν eig c I degree amp r h g hh h0 hg g0 a ha
  · exact priorNamespacedMeanPressure_field_insert hhaar hgauss hN μ hμ ν eig c I degree amp r h g hh h0 hg g0 0 le_rfl

end InvariantIsing

end

end OAI
