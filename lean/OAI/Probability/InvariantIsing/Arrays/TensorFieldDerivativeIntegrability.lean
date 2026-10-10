import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivative
import OAI.Probability.InvariantIsing.Arrays.TensorGaussianMean

namespace OAI

/-! Integrability of the tensor pressure before varying its
linear field. Gaussian CGF bounds suffice; no concentration input is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma randomCoefficient_log_partition_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω → X → ℝ) (hH : Measurable (Function.uncurry H))
    (he : ∀ ω, Integrable (fun x => Real.exp (H ω x)) (ν ω))
    (hi : Integrable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) P)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hcap : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) :
    Integrable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1))
      (P.prod gaussianCoordinates) := by
  let η := fun ω => (ν ω).tilted (H ω)
  have : ∀ ω, IsProbabilityMeasure (η ω) := fun ω => isProbabilityMeasure_tilted (he ω)
  have hη : Measurable η := measurable_random_tilted_measure
    (ν := ν) (H := Function.uncurry H) hν hH
  let G := fun p : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A p.1 x) p.2) (η p.1) 1
  have hmG : Measurable G := measurable_randomCoefficient_cgf hη A hA 1
  have hiG : Integrable G (P.prod gaussianCoordinates) := integrable_randomCoefficient_cgf hη A hA hcap 1
  have hmC : Measurable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) :=
    (measurable_random_referencePartition hν hH).log
  have : ∀ p : Ω × (ℕ → ℝ), IsProbabilityMeasure ((ν ∘ Prod.fst) p) := fun p => by
    change IsProbabilityMeasure (ν p.1)
    infer_instance
  have hHm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => H p.1.1 p.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hmF : Measurable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) :=
    (measurable_random_referencePartition (hν.comp measurable_fst) (hHm.add hA)).log
  have hfold : (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) =ᵐ[P.prod gaussianCoordinates]
      (fun p => Real.log (∫ x, Real.exp (H p.1 x) ∂ν p.1) + G p) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmF ((hmC.comp measurable_fst).add hmG))).mpr
    exact ae_of_all _ fun ω => by
      have ht := cylinder_log_partition_base (ν ω) (H ω) (he ω) (A ω) (hcap ω) 1
      filter_upwards [ht] with z hz
      simpa only [one_mul, G, η, Pi.add_apply, Function.comp_apply] using hz
  exact ((hi.comp_fst gaussianCoordinates).add hiG).congr hfold.symm

lemma tensorDeterministicLog_eq {N n : ℕ} (eig c : Fin N → ℝ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
      (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
      ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) =
      logPartition (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ) := by
  unfold labeledSpinReference
  rw [integral_fun_fst (μ := (uniformSpinPrior N : Measure (Spin N)))
    (ν := labeledLeafLaw n ω.2) (fun σ => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))]
  simp only [probReal_univ, one_smul]
  exact finiteLogIntegral_uniformSpinPrior _

lemma tensorDeterministicLog_abs_le {N : ℕ} (eig c : Fin N → ℝ)
    (U : Rotation N) :
    |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)| ≤
      (∑ i, |eig i|) * N / 2 + ∑ i, |c i| := by
  have he (σ : Spin N) : |rotatedEnergy eig U σ| ≤ (∑ i, |eig i|) * N / 2 := by
    have ht := abs_rotatedEnergy_sub_le eig (fun _ => 0) U (∑ i, |eig i|)
      (fun i => by simpa only [sub_zero] using
        (Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i))) σ
    simpa only [rotatedEnergy, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero] using ht
  have hf (σ : Spin N) : |fieldEnergy c σ| ≤ ∑ i, |c i| := by
    simpa only [fieldEnergy, zero_mul, Finset.sum_const_zero, sub_zero] using
      abs_fieldEnergy_sub_le c (fun _ => 0) σ
  have ht := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) (fun _ : Spin N => 0)
    ((∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    (fun σ => by simpa only [sub_zero] using (abs_add_le _ _).trans (add_le_add (he σ) (hf σ)))
  simpa only [logPartition_zero, sub_zero] using ht

def tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (ω : SpecialOrthogonal N × LabeledTree n) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1

lemma measurable_tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (Function.uncurry (tensorDeterministicEnergy eig c n)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add_const (fieldEnergy c x.1)

lemma tensorDeterministicLog_integrable {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) :
    Integrable (fun ω : SpecialOrthogonal N × LabeledTree n => Real.log
      (∫ x, Real.exp (tensorDeterministicEnergy eig c n ω x)
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2))
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  apply integrable_of_measurable_abs_le (c := (∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    ((measurable_random_referencePartition (ν := ν)
      (H := Function.uncurry (tensorDeterministicEnergy eig c n)) hν
        (measurable_tensorDeterministicEnergy eig c n)).log)
  intro ω
  change |Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)| ≤ _
  rw [tensorDeterministicLog_eq]
  exact tensorDeterministicLog_abs_le eig c (specialRotation ω.1)

lemma measurable_tensorNamespacedPathFields {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
        (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amp n
        (fun a => tensorPathProfile I degree n treeDegree h a) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → NNReal :=
    fun a => tensorPathProfile I degree n treeDegree h a
  have hm : Measurable (fun p : TensorFlatDisorder N n => (p.1.1, p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amp n v x).comp hm
  convert hf using 1
  rfl

theorem tensorNamespacedLog_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (tensorNamespacedLog eig c I degree amp n treeDegree h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  exact randomCoefficient_log_partition_integrable hν (tensorDeterministicEnergy eig c n)
    (measurable_tensorDeterministicEnergy eig c n)
    (fun ω => finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (tensorDeterministicLog_integrable μ eig c n b)
    (fun ω => tensorNamespacedCoefficients (specialRotation ω.1) I degree amp n
      (fun a => tensorPathProfile I degree n treeDegree h a))
    (measurable_tensorNamespacedPathFields I degree amp n treeDegree h)
    (fun ω x => tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amp n treeDegree h hh h0 x)

lemma tensorNamespacedPressure_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (tensorNamespacedPressure eig c I degree amp n treeDegree h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) :=
  (tensorNamespacedLog_integrable μ eig c I degree amp n b treeDegree h hh h0).const_mul _

end InvariantIsing

end

end OAI
