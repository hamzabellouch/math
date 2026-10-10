import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFlatMean
import OAI.Probability.InvariantIsing.Arrays.TensorProfiles
import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights
import OAI.Probability.IsingPerceptron.VarianceDerivative

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private abbrev TensorGaussianKey {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) := ℕ × List ChildLabel × SpinTensorIndex I degree

/-- Namespace zero contains the linear field; namespace `j+1` contains
precisely the `j`th spectral tensor at all ancestor levels. -/
def tensorNamespaceTag {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (q : TensorGaussianKey I degree) : ℕ :=
  match q.2.2 with
  | Sum.inl a => Nat.pair 0 (Encodable.encode (q.1, q.2.1, a))
  | Sum.inr a => Nat.pair (a.1 + 1) (Encodable.encode (q.1, q.2.1, a.2))

lemma tensorNamespaceTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : Function.Injective (tensorNamespaceTag I degree) := by
  rintro ⟨i, p, a⟩ ⟨j, q, b⟩ h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      cases he
      rfl
    | inr b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨a, s⟩
      rcases b with ⟨b, t⟩
      have hp := Nat.pair_eq_pair.mp h
      have hab : a = b := Fin.ext (Nat.add_right_cancel hp.1)
      subst b
      have he := Encodable.encode_inj.mp hp.2
      cases he
      rfl

def tensorNamespacedCoefficients {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
    tensorNamespaceTag I degree (i.1, (labeledAddress n x.2).take i.1, i.2))
    (fun i => (NNReal.sqrt (v i.1 i.2) : ℝ) * spinTensorFeature U I degree amplitude x.1 i.2)

/-- Injective Gaussian reindexing identifies the entire countable
spin/leaf field law with the flat tensor model. -/
theorem tensorNamespacedFields_law {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) := by
  let Φ := fun (G : TensorGaussianKey I degree → ℝ) (x : Spin N × LabeledLeaf n) =>
    ∑ i : Fin (n + 1), ∑ a : SpinTensorIndex I degree,
      (NNReal.sqrt (v i a) : ℝ) * spinTensorFeature U I degree amplitude x.1 a *
        G (i, (labeledAddress n x.2).take i, a)
  have hmΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro x
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun a _ =>
      (measurable_pi_apply (i.1, (labeledAddress n x.2).take i, a)).const_mul _
  have he : (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q : TensorGaussianKey I degree => g (Encodable.encode q)) := by
    funext g x
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hn : (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q => g (tensorNamespaceTag I degree q)) := by
    funext g x
    rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hp := gaussian_pullback_measurePreserving
    (Encodable.encode : TensorGaussianKey I degree → ℕ) Encodable.encode_injective
  have hq := gaussian_pullback_measurePreserving
    (tensorNamespaceTag I degree) (tensorNamespaceTag_injective I degree)
  rw [he, hn, ← Measure.map_map hmΦ hp.measurable, ← Measure.map_map hmΦ hq.measurable,
    hp.map_eq, hq.map_eq]

private lemma sqrt_varianceIncrement {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    (NNReal.sqrt (varianceIncrement q i) : ℝ) = pathAmplitude q i := by
  rw [Real.coe_sqrt, varianceIncrement_coe hq h0]
  rfl

def tensorLinearCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n x.2 (fun i => pathAmplitude h i) (fun i => spinValue (x.1 i))

/-- The reindexed field is exactly the sum of the linear enrichment and
the displayed independent spectral/tree Gaussian monomials. -/
theorem tensorNamespacedField_expand {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x) g =
      cylinderField (tensorLinearCoefficients n h x) (fun i => g (Nat.pair 0 i)) +
        ∑ j, amplitude j * cylinderField
          (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x)
          (fun i => g (Nat.pair (j + 1) i)) := by
  rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorPathProfile, tensorVarianceProfile, spinTensorFeature, tensorNamespaceTag]
  simp_rw [sqrt_varianceIncrement hh h0,
    sqrt_varianceIncrement (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [tensorLinearCoefficients, treeFieldCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [jointSpectralMonomialCoefficients, treeFieldCoefficients, cylinderField_feature,
      Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [treeFeatureTag]
    ring

lemma tensorNamespacedField_frozen {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (x : Spin N × LabeledLeaf n) (z : ℕ → ℝ) (g : OtherNamespaces (j + 1)) :
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (z, g)) =
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, g)) := by
  classical
  simp_rw [tensorNamespacedField_expand U I degree _ n treeDegree h hh h0]
  congr 1
  · congr 1
    funext i
    exact (gaussianNamespaceJoin_other (j + 1) z g ⟨0, by omega⟩ i).trans
      (gaussianNamespaceJoin_other (j + 1) 0 g ⟨0, by omega⟩ i).symm
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = j
    · subst a
      simp
    · simp only [Function.update_of_ne ha]
      congr 1
      congr 1
      funext i
      have hv : (a : ℕ) + 1 ≠ (j : ℕ) + 1 := fun he => ha (Fin.ext (Nat.add_right_cancel he))
      exact (gaussianNamespaceJoin_other (j + 1) z g ⟨a + 1, hv⟩ i).trans
        (gaussianNamespaceJoin_other (j + 1) 0 g ⟨a + 1, hv⟩ i).symm

/-- Inserting the selected standard Gaussian family adds exactly its
actual amplitude times `jointSpectralMonomialCoefficients`. -/
theorem tensorNamespacedField_insert {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (x : Spin N × LabeledLeaf n) (z : ℕ → ℝ) (g : OtherNamespaces (j + 1)) :
    cylinderField (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (z, g)) =
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, g)) +
        amplitude j * cylinderField (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x) z := by
  classical
  rw [← tensorNamespacedField_frozen U I degree amplitude n treeDegree h hh h0 j x z g]
  simp_rw [tensorNamespacedField_expand U I degree _ n treeDegree h hh h0]
  let Y := fun a : Fin k => cylinderField
    (jointSpectralMonomialCoefficients U I (degree a) n (treeDegree a) x)
    (fun i => gaussianNamespaceJoin (j + 1) (z, g) (Nat.pair (a + 1) i))
  have he (a : Fin k) : amplitude a * Y a = Function.update amplitude j 0 a * Y a +
      if a = j then amplitude j * Y j else 0 := by
    by_cases ha : a = j
    · subst a; simp
    · simp [ha]
  change _ + ∑ a, amplitude a * Y a = _
  have hsum : (∑ a, amplitude a * Y a) =
      ∑ a, (Function.update amplitude j 0 a * Y a + if a = j then amplitude j * Y j else 0) :=
    Finset.sum_congr rfl (fun a _ => he a)
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hY : Y j = cylinderField (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x) z := by
    simp only [Y, gaussianNamespaceJoin_selected]
  rw [hY]
  ring
lemma measurable_tensorNamespacedFields_joint {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) := by
  simp only [tensorNamespacedCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (tensorNamespaceTag I degree (i.1.1, (labeledAddress n x.2).take i.1, i.2))).comp measurable_snd)

/-- The full finite-volume Gibbs-law distribution is preserved by the
Gaussian namespace reindexing, for each actual rotation and cascade prior. -/
theorem tensorNamespacedGibbs_law {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (T : LabeledTree n) :
    let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
    let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig U x.1 + fieldEnergy c x.1
    gaussianCoordinates.map (fun g => gibbsProbability ν
      (fun x => H x + cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g)) =
    gaussianCoordinates.map (fun g => gibbsProbability ν
      (fun x => H x + cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g)) := by
  intro ν H
  let Kern := fun F : (Spin N × LabeledLeaf n → ℝ) => gibbsProbability ν (fun x => H x + F x)
  have : ∀ F : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) F) :=
    fun _ => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      infer_instance
  have hE : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hc : Measurable (fun _ : (Spin N × LabeledLeaf n → ℝ) => H x) := measurable_const
    exact hc.add (measurable_pi_apply x)
  have hmKern : Measurable Kern := measurable_gibbsProbability (ν := fun _ : (Spin N × LabeledLeaf n → ℝ) => ν)
    (H := fun p => H p.2 + p.1 p.2) measurable_const hE
  have hleft : Measurable (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hright : Measurable (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  change gaussianCoordinates.map (Kern ∘ (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g)) =
    gaussianCoordinates.map (Kern ∘ (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g))
  rw [← Measure.map_map hmKern hleft, ← Measure.map_map hmKern hright, tensorNamespacedFields_law]

abbrev TensorFrozenData (N n : ℕ) (j : ℕ) := (SpecialOrthogonal N × LabeledTree n) × OtherNamespaces (j + 1)

def tensorFrozenLaw {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    Measure (TensorFrozenData N n j) :=
  (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod (otherNamespacesLaw (j + 1))

instance tensorFrozenLaw_probability {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (n : ℕ) (b : ℕ → ℝ) (j : ℕ) : IsProbabilityMeasure (tensorFrozenLaw μ n b j) := by
  unfold tensorFrozenLaw
  infer_instance

def tensorFrozenBaseEnergy {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
      (Function.update amplitude j 0) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, ω.2))

def tensorFrozenReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.1.2)
    (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j ω)

instance tensorFrozenReference_probability {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (ω : TensorFrozenData N n j) :
    IsProbabilityMeasure (tensorFrozenReference eig c I degree amplitude n treeDegree h j ω) :=
  gibbsProbability_probability _ _

lemma measurable_tensorFrozenBaseEnergy {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (Function.uncurry (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j)) := by
  change Measurable (fun p : TensorFrozenData N n j × (Spin N × LabeledLeaf n) =>
    tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j p.1 p.2)
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun ω : TensorFrozenData N n j =>
    rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (gaussianNamespaceJoin (j + 1) (0, ω.2)))
  have hrot0 : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  have hrot : Measurable (fun ω : TensorFrozenData N n j => rotatedEnergy eig (specialRotation ω.1.1) x.1) :=
    hrot0.comp measurable_fst.fst
  have hm : Measurable (fun ω : TensorFrozenData N n j =>
      (ω.1.1, gaussianNamespaceJoin (j + 1) (0, ω.2))) :=
    measurable_fst.fst.prodMk ((measurable_gaussianNamespaceJoin (j + 1)).comp
      (measurable_const.prodMk measurable_snd))
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hfield0 := measurable_tensorNamespacedFields_joint I degree
    (Function.update amplitude j 0) n v x
  have hfield : Measurable (fun ω : TensorFrozenData N n j =>
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n v x) (gaussianNamespaceJoin (j + 1) (0, ω.2))) := by
    convert hfield0.comp hm using 1
    rfl
  convert (hrot.add_const (fieldEnergy c x.1)).add hfield using 1

lemma measurable_tensorFrozenReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (tensorFrozenReference eig c I degree amplitude n treeDegree h j) := by
  have : ∀ ω : TensorFrozenData N n j, IsProbabilityMeasure
      ((labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ∘ (fun ω : TensorFrozenData N n j => ω.1.2)) ω) :=
    fun ω => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.1.2)
      infer_instance
  exact measurable_gibbsProbability
    (H := Function.uncurry (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j))
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd)
    (measurable_tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j)

theorem tensorFrozenEnergy_insert {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (ω : TensorFrozenData N n j) (z : ℕ → ℝ) (x : Spin N × LabeledLeaf n) :
    rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (gaussianNamespaceJoin (j + 1) (z, ω.2)) =
      tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j ω x +
        amplitude j * cylinderField (jointSpectralMonomialCoefficients
          (specialRotation ω.1.1) I (degree j) n (treeDegree j) x) z := by
  rw [tensorNamespacedField_insert (specialRotation ω.1.1) I degree amplitude n treeDegree h hh h0 j x z ω.2]
  exact (add_assoc _ _ _).symm

/-- The selected field is a genuinely independent Gaussian product factor;
all remaining marks, the rotation, and the tree form external disorder. -/
theorem tensorFrozenInsertion_measurePreserving {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    MeasurePreserving (fun p : TensorFrozenData N n j × (ℕ → ℝ) =>
      (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2)))
      ((tensorFrozenLaw μ n b j).prod gaussianCoordinates)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) :=
  namespaceInsertion_preserving _ _

end InvariantIsing

end

end OAI
