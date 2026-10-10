import OAI.Probability.InvariantIsing.Arrays.NSpinTensorLabeled
import OAI.Probability.InvariantIsing.Arrays.TensorLeafCoefficients

namespace OAI

/-! The flat countable Gaussian field has the actual root/forest mark law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorNodeTag {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (w : Option (ForestVertex n))
    (i : SpinTensorIndex I degree) : ℕ :=
  Encodable.encode ((nodeAddress n w).length, nodeAddress n w, i)

lemma tensorNodeTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × SpinTensorIndex I degree =>
      tensorNodeTag I degree n p.1 p.2) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have he := Encodable.encode_inj.mp h
  exact Prod.ext (nodeAddress_injective n (congrArg (fun p => p.2.1) he))
    (congrArg (fun p => p.2.2) he)

lemma tensorNodeTag_nodeAt {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (leaf : LabeledLeaf n)
    (level : Fin (n + 1)) (i : SpinTensorIndex I degree) :
    tensorNodeTag I degree n (nodeAt n leaf level) i = treeFeatureTag n leaf (level, i) := by
  unfold tensorNodeTag treeFeatureTag
  rw [nodeAddress_nodeAt_length, nodeAddress_nodeAt]

def tensorStandardGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (g : ℕ → ℝ)
    (w : Option (ForestVertex n)) (i : SpinTensorIndex I degree) : ℝ :=
  g (tensorNodeTag I degree n w i)

lemma measurable_tensorStandardGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) : Measurable (tensorStandardGaussianNodes I degree n) := by
  unfold tensorStandardGaussianNodes
  fun_prop

theorem tensorStandardGaussianNodes_law {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    gaussianCoordinates.map (tensorStandardGaussianNodes I degree n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)) := by
  let t := fun p : Option (ForestVertex n) × SpinTensorIndex I degree => tensorNodeTag I degree n p.1 p.2
  have hp := gaussian_pullback_measurePreserving t (tensorNodeTag_injective I degree n)
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (SpinTensorIndex I degree) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable, hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : SpinTensorIndex I degree) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

private theorem tensorMarkScale_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun z : SpinTensorIndex I degree → ℝ => fun i => (NNReal.sqrt (v i) : ℝ) * z i)
      (Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ)) := by
  change MeasurePreserving _ _ (Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i)))
  apply measurePreserving_pi
  intro i
  refine ⟨by fun_prop, ?_⟩
  have hs : NNReal.mk ((NNReal.sqrt (v i) : ℝ) ^ 2) (sq_nonneg _) = v i := by
    apply Subtype.ext
    change (NNReal.sqrt (v i) : ℝ) ^ 2 = (v i : ℝ)
    exact_mod_cast NNReal.sq_sqrt (v i)
  simpa only [hs, mul_zero, mul_one] using
    gaussianReal_map_const_mul (μ := 0) (v := 1) (NNReal.sqrt (v i) : ℝ)

def tensorGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (g : ℕ → ℝ) (w : Option (ForestVertex n)) (i : SpinTensorIndex I degree) : ℝ :=
  (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * tensorStandardGaussianNodes I degree n g w i

lemma measurable_tensorGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (tensorGaussianNodes I degree n v) := by
  unfold tensorGaussianNodes tensorStandardGaussianNodes
  fun_prop

theorem tensorGaussianNodes_measurePreserving {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorGaussianNodes I degree n v) gaussianCoordinates
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
  have hstd : MeasurePreserving (tensorStandardGaussianNodes I degree n) gaussianCoordinates
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))) :=
    ⟨measurable_tensorStandardGaussianNodes I degree n, tensorStandardGaussianNodes_law I degree n⟩
  have hscale : MeasurePreserving
      (fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
        fun w i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * q w i)
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)))
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.infinitePi_map_pi (f := fun w (z : SpinTensorIndex I degree → ℝ) =>
      fun i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * z i) _ (fun _ => by fun_prop)]
    apply congrArg Measure.infinitePi
    funext w
    exact (tensorMarkScale_measurePreserving I degree (v (nodeAddress n w).length)).map_eq
  exact hscale.comp hstd

/-- The root and all forest coordinates have their independent prescribed
Gaussian laws, including zero variances. -/
theorem tensorGaussianRootForest_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun g => (tensorGaussianNodes I degree n v g none,
      fun w => tensorGaussianNodes I degree n v g (some w))) gaussianCoordinates
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (Measure.infinitePi (fun w : ForestVertex n =>
          (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
            Measure (SpinTensorIndex I degree → ℝ))))) := by
  refine ⟨by unfold tensorGaussianNodes tensorStandardGaussianNodes; fun_prop, ?_⟩
  change gaussianCoordinates.map ((fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
      (q none, fun w => q (some w))) ∘ tensorGaussianNodes I degree n v) = _
  rw [← Measure.map_map (by fun_prop) (measurable_tensorGaussianNodes I degree n v),
    (tensorGaussianNodes_measurePreserving I degree n v).map_eq]
  have he := infinitePi_option_split
    (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
    (fun w : ForestVertex n => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
      Measure (SpinTensorIndex I degree → ℝ)))
  have hc : (fun w : Option (ForestVertex n) => w.elim
      (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
      (fun w => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
        Measure (SpinTensorIndex I degree → ℝ)))) =
      (fun w => (tensorGaussianLaw I degree (v (nodeAddress n w).length) :
        Measure (SpinTensorIndex I degree → ℝ))) := by
    funext w
    cases w with
    | none => cases n <;> rfl
    | some w => simp only [Option.elim_some, nodeAddress_length_some]
  simpa only [hc] using he

lemma cylinderField_tensorLeaf_nodes {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (σ : Spin N) (leaf : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      spinTensorEnergy U I degree amplitude (tensorGaussianNodes I degree n v g none) σ +
      ∑ i : Fin n, spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (some (edgeAt n leaf i))) σ := by
  classical
  have he : cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      ∑ i : Fin (n + 1), spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (nodeAt n leaf i)) σ := by
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    unfold spinTensorEnergy tensorGaussianNodes tensorStandardGaussianNodes
    rw [nodeAddress_nodeAt_length]
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorNodeTag_nodeAt]
    ring
  rw [he, Fin.sum_univ_succ]
  simp only [nodeAt_zero, nodeAt_succ]

def tensorFlatToCoordinates {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × TensorCoordinateData I degree n :=
  (tensorGaussianNodes I degree n v p.2 none,
    (p.1, fun w => tensorGaussianNodes I degree n v p.2 (some w)))

theorem tensorFlatToCoordinates_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToCoordinates I degree n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorCoordinateLaw I degree n b (fun i => v (i + 1)))) := by
  let R := (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
  let T := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := Measure.infinitePi (fun w : ForestVertex n =>
    (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) : Measure (SpinTensorIndex I degree → ℝ)))
  have hswap : MeasurePreserving Prod.swap (T.prod R) (R.prod T) := Measure.measurePreserving_swap
  have hshuffle := (measurePreserving_prodAssoc R T F).comp
    ((hswap.prod (MeasurePreserving.id F)).comp
      ((measurePreserving_prodAssoc T R F).symm MeasurableEquiv.prodAssoc))
  have hprod := (MeasurePreserving.id T).prod (tensorGaussianRootForest_measurePreserving I degree n v)
  convert hshuffle.comp hprod using 1
  all_goals rfl

def tensorFlatToLabeled {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n :=
  let q := tensorFlatToCoordinates I degree n v p
  (q.1, tensorEnergyCoordinates U I degree amplitude n q.2)

/-- The flat Gaussian spin/leaf model is exactly the independent Gaussian
root and tensor-energy forest model used by the cascade recursion. -/
theorem tensorFlatToLabeled_measurePreserving {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToLabeled U I degree amplitude n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorLabeledLaw U I degree amplitude n b (fun i => v (i + 1)))) := by
  have h := ((MeasurePreserving.id
    (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))).prod
      (tensorEnergyCoordinates_measurePreserving U I degree amplitude n b (fun i => v (i + 1)))).comp
    (tensorFlatToCoordinates_measurePreserving I degree n b v)
  convert h using 1
  all_goals rfl

theorem tensorLabeledEnergy_flat_eq {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) :
    let q := tensorFlatToLabeled U I degree amplitude n v p
    tensorLabeledEnergy eig U c I degree amplitude n q.1 q.2 x =
      rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x) p.2 := by
  rw [cylinderField_tensorLeaf_nodes]
  dsimp only [tensorFlatToLabeled, tensorFlatToCoordinates, tensorLabeledEnergy,
    cascadeCoordinateEnergy, tensorSpinBaseEnergy, tensorEnergyCoordinates]
  ring

end InvariantIsing

end

end OAI
