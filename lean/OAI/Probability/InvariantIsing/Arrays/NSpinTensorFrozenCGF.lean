import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozen
import OAI.Probability.InvariantIsing.Pressure.RandomCoefficientIBP

namespace OAI

/-! Actual frozen exponential integrability and selected-field log partition identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespacedCoefficients_variance_eq {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) =
      (tensorLeafCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) := by
  have hi : Function.Injective (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
      tensorNamespaceTag I degree (i.1.1, (labeledAddress n x.2).take i.1, i.2)) := by
    intro i j hij
    apply treeFeatureTag_injective n x.2
    exact congrArg Encodable.encode ((tensorNamespaceTag_injective I degree) hij)
  rw [tensorNamespacedCoefficients, featureCoefficients_variance _ hi,
    tensorLeafCoefficients, featureCoefficients_variance _ (treeFeatureTag_injective n x.2)]

lemma tensorNamespacedPath_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x).sum (fun _ c => c ^ 2) ≤
      h n * N + ∑ j, amplitude j ^ 2 := by
  rw [tensorNamespacedCoefficients_variance_eq]
  exact tensorPathProfile_variance_cap U I degree amplitude n treeDegree h hh h0 x

private lemma measurable_tensorBaseEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1 + fieldEnergy c p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  have hrot : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  exact (hrot.comp measurable_fst).add_const (fieldEnergy c x.1)

private lemma tensorBase_exp_integrable {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Integrable (fun x : Spin N × LabeledLeaf n =>
      Real.exp (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1))
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) :=
  (Integrable.of_finite : Integrable
    (fun σ : Spin N => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (uniformSpinPrior N : Measure (Spin N))).comp_fst (labeledLeafLaw n ω.2)

private lemma measurable_namespacedPathField {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : ((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hm : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hm
  convert hf using 1
  rfl

private lemma measurable_frozenSelectedField {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (j : Fin k) :
    Measurable (fun p : (TensorFrozenData N n j × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (jointSpectralMonomialCoefficients
        (specialRotation p.1.1.1.1) I (degree j) n (treeDegree j) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have hp : Measurable (fun p : TensorFrozenData N n j × (ℕ → ℝ) => (p.1.1.1, p.2)) :=
    measurable_fst.fst.fst.prodMk measurable_snd
  have hf := (measurable_jointSpectralMonomialField I (degree j) n (treeDegree j) x).comp hp
  convert hf using 1
  rfl

/-- Exponentials of the tensor Hamiltonian are integrable for
almost every joint rotation/tree/Gaussian disorder. No concentration or
limiting-pressure hypothesis is used. -/
theorem tensorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) := tensorBase_exp_integrable eig c n ω
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorBaseEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_namespacedPathField I degree amplitude n treeDegree h
  have hA (ω : Ω) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amplitude n treeDegree h hh h0 x
  have he := randomCoefficient_all_exp_ae
    (P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) htilt A hAm hA
  filter_upwards [he] with p hp
  have hi := hp 1
  rw [integrable_tilted_iff (hbase p.1)] at hi
  simpa only [H, A, ν, one_mul, smul_eq_mul, ← Real.exp_add] using hi

/-- The frozen base energy is the actual Hamiltonian with the selected
amplitude set to zero, and is exponentially integrable almost surely. -/
theorem tensorFrozenBase_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) :
    ∀ᵐ ω : TensorFrozenData N n j ∂tensorFrozenLaw μ n b j,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j ω x))
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.1.2) := by
  have hp := tensorFrozenInsertion_measurePreserving μ n b j
  have he := hp.quasiMeasurePreserving.ae
    (tensorNamespaced_exp_integrable_ae μ eig c I degree (Function.update amplitude j 0)
      n b treeDegree h hh h0)
  have he' : ∀ᵐ p : TensorFrozenData N n j × (ℕ → ℝ)
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j p.1 x))
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2) := by
    filter_upwards [he] with p hp
    convert hp using 1
    funext x
    congr 1
    dsimp only [tensorFrozenBaseEnergy]
    rw [tensorNamespacedField_frozen (specialRotation p.1.1.1) I degree amplitude n treeDegree h hh h0 j x p.2 p.1.2]
  filter_upwards [Measure.ae_ae_of_ae_prod he'] with ω hω
  obtain ⟨z, hz⟩ := hω.exists
  exact hz


def tensorNamespacedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)

def tensorFrozenPartitionLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  tensorNamespacedLog eig c I degree (Function.update amplitude j t) n treeDegree h
    (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2))

def tensorFrozenCGF {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
      (specialRotation p.1.1.1) I (degree j) n (treeDegree j) x) p.2)
    (tensorFrozenReference eig c I degree amplitude n treeDegree h j p.1) t

lemma measurable_tensorFrozenCGF {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ) :
    Measurable (tensorFrozenCGF eig c I degree amplitude n treeDegree h j t) := by
  let A := fun (ω : TensorFrozenData N n j) =>
    jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (treeDegree j)
  let ν := tensorFrozenReference eig c I degree amplitude n treeDegree h j
  have hm : Measurable (fun p : (TensorFrozenData N n j × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_frozenSelectedField I degree n treeDegree j
  have hf := measurable_randomCoefficient_cgf (ν := ν)
    (measurable_tensorFrozenReference eig c I degree amplitude n treeDegree h j) A hm t
  convert hf using 1
  rfl

/-- The selected-field CGF is an actual square-integrable observable on
the frozen external disorder and independent Gaussian factor. -/
theorem tensorFrozenCGF_memLp_two {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ) :
    MemLp (tensorFrozenCGF eig c I degree amplitude n treeDegree h j t) 2
      ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) := by
  have hm := measurable_tensorFrozenCGF eig c I degree amplitude n treeDegree h j t
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact joint_integrable_square_of_uniform_conditionals
    (P := tensorFrozenLaw μ n b j) hm
    (fun ω => (cylinder_cgf_second
      (tensorFrozenReference eig c I degree amplitude n treeDegree h j ω)
      (jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (treeDegree j))
      (jointSpectralMonomialCoefficients_variance_le_one (specialRotation ω.1.1) I (degree j) n (treeDegree j)) t).1)
    (fun ω => (cylinder_cgf_second
      (tensorFrozenReference eig c I degree amplitude n treeDegree h j ω)
      (jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (treeDegree j))
      (jointSpectralMonomialCoefficients_variance_le_one (specialRotation ω.1.1) I (degree j) n (treeDegree j)) t).2)

/-- The CGF is exactly the difference of the actual log partitions at
selected amplitude `t` and selected amplitude zero, almost surely. -/
theorem tensorFrozenCGF_eq_log_difference {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (t : ℝ) :
    tensorFrozenCGF eig c I degree amplitude n treeDegree h j t =ᵐ[
      (tensorFrozenLaw μ n b j).prod gaussianCoordinates]
    (fun p => tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j t p -
      tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j 0 p) := by
  have hp := tensorFrozenInsertion_measurePreserving μ n b j
  have hbase := (measurePreserving_fst (μ := tensorFrozenLaw μ n b j) (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (tensorFrozenBase_exp_integrable_ae μ eig c I degree amplitude n b treeDegree h hh h0 j)
  have hfull := hp.quasiMeasurePreserving.ae
    (tensorNamespaced_exp_integrable_ae μ eig c I degree (Function.update amplitude j t)
      n b treeDegree h hh h0)
  filter_upwards [hbase, hfull] with p hb hf
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2
  let H := tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j p.1
  let Y := fun x : Spin N × LabeledLeaf n => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (treeDegree j) x) p.2
  have henergy (a : ℝ) (x : Spin N × LabeledLeaf n) :
      rotatedEnergy eig (specialRotation p.1.1.1) x.1 + fieldEnergy c x.1 +
        cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree
          (Function.update amplitude j a) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
          (gaussianNamespaceJoin (j + 1) (p.2, p.1.2)) = H x + a * Y x := by
    have he := tensorFrozenEnergy_insert eig c I degree (Function.update amplitude j a)
      n treeDegree h hh h0 j p.1 p.2 x
    simpa only [tensorFrozenBaseEnergy, Function.update_idem, Function.update_self, H, Y] using he
  have hpart (a : ℝ) : tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j a p =
      Real.log (∫ x, Real.exp (H x + a * Y x) ∂ν) := by
    apply congrArg Real.log
    apply integral_congr_ae
    exact ae_of_all _ fun x => congrArg Real.exp (henergy a x)
  have hi : Integrable (fun x => Real.exp (H x + t * Y x)) ν := by
    convert hf using 1
    funext x
    exact congrArg Real.exp (henergy t x).symm
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := integral_exp_pos hb
  have hz' : 0 < ∫ x, Real.exp (H x + t * Y x) ∂ν := integral_exp_pos hi
  rw [hpart t, hpart 0]
  simp only [zero_mul, add_zero]
  change Real.log (∫ x, Real.exp (t * Y x) ∂gibbsProbability ν H) = _
  rw [gibbsProbability_eq_tilted ν H hb, integral_exp_tilted H (fun x => t * Y x)]
  change Real.log ((∫ x, Real.exp (H x + t * Y x) ∂ν) / ∫ x, Real.exp (H x) ∂ν) = _
  exact Real.log_div hz'.ne' hz.ne'

end InvariantIsing

end

end OAI
