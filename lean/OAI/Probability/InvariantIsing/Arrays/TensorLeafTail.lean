import OAI.Probability.InvariantIsing.Arrays.NSpinTensorGaussianLaw
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! The scalar prefix test in the actual finite tensor model. The root is
averaged after the cascade marking identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal

namespace InvariantIsing

def tensorLeafPrefixTest {N n : ℕ} (d : Fin n)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : ℝ :=
  if (labeledAddress n (σ 1).2).take (d + 1) =
    (labeledAddress n (σ 0).2).take (d + 1) then 1 else 0

lemma tensorLeafPrefixTest_abs_le {N n : ℕ} (d : Fin n)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : |tensorLeafPrefixTest d σ| ≤ 1 := by
  unfold tensorLeafPrefixTest
  split_ifs <;> norm_num

lemma tensorFlat_leafPrefix_mean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d : Fin n) :
    (∫ p : LabeledTree n × (ℕ → ℝ),
      referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
        (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
          cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
        (tensorLeafPrefixTest d)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) = 1 - b d := by
  let F := fun p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    referenceReplicaMean (tensorLabeledReference N n p.2)
      (tensorLabeledEnergy eig U c I degree amp n p.1 p.2) (tensorLeafPrefixTest d)
  have : ∀ p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n,
      IsProbabilityMeasure ((tensorLabeledReference N n ∘ Prod.snd) p) := fun p => by
    dsimp only [Function.comp_apply]
    infer_instance
  have hF : Measurable F := measurable_random_referenceReplicaMean
    ((measurable_tensorLabeledReference N n).comp measurable_snd)
    (measurable_tensorLabeledEnergy_root eig U c I degree amp n)
    ((measurable_of_countable (tensorLeafPrefixTest (N := N) d)).comp measurable_snd)
  have hFb p : |F p| ≤ 1 := referenceReplicaMean_abs_le _ _ _
    (measurable_of_countable _) zero_le_one (tensorLeafPrefixTest_abs_le d)
  have hi : Integrable F
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorLabeledLaw U I degree amp n b (fun i => v (i + 1)))) :=
    integrable_of_measurable_abs_le hF hFb
  calc
    _ = ∫ p, F (tensorFlatToLabeled U I degree amp n v p)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates := by
      apply integral_congr_ae
      refine ae_of_all _ fun p => ?_
      dsimp only [F]
      have he : tensorLabeledEnergy eig U c I degree amp n
          (tensorFlatToLabeled U I degree amp n v p).1
          (tensorFlatToLabeled U I degree amp n v p).2 =
          fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
            cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2 := by
        funext x
        exact tensorLabeledEnergy_flat_eq eig U c I degree amp n v p x
      rw [he]
      rfl
    _ = ∫ p, F p ∂(tensorGaussianLaw I degree (v 0) : Measure _).prod
        (tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))) :=
      (tensorFlatToLabeled_measurePreserving U I degree amp n b v).hasLaw.integral_comp
        hF.aestronglyMeasurable
    _ = ∫ z, ∫ T, F (z,T) ∂tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))
        ∂(tensorGaussianLaw I degree (v 0) : Measure _) := integral_prod _ hi
    _ = 1 - b d := by
      have he (z : SpinTensorIndex I degree → ℝ) :
          (∫ T, F (z,T) ∂tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))) = 1 - b d :=
        tensorLabeled_tilted_parent_tail hN eig U c I degree amp n b _ hb z d
      simp_rw [he]
      simp only [integral_const, probReal_univ, one_smul]


lemma tensorGaussian_replicaMean_namespace {N m k r : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (T : LabeledTree n) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (D : (Fin r → Spin N × LabeledLeaf n) → ℝ) :
    (∫ z, referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorLeafCoefficients U I degree amp n v x) z) D ∂gaussianCoordinates) =
    (∫ z, referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorNamespacedCoefficients U I degree amp n v x) z) D ∂gaussianCoordinates) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig U x.1 + fieldEnergy c x.1
  let F := fun f : Spin N × LabeledLeaf n → ℝ => referenceReplicaMean ν (fun x => H x + f x) D
  have hν : Measurable (fun _ : (Spin N × LabeledLeaf n → ℝ) => ν) := measurable_const
  have : ∀ f : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) f) :=
    fun _ => inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) T))
  have hH : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) =>
      H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (show Measurable (fun _ : (Spin N × LabeledLeaf n → ℝ) => H x) from
      measurable_const).add (measurable_pi_apply x)
  have hF : Measurable F := measurable_random_referenceReplicaMean hν hH
    ((measurable_of_countable D).comp measurable_snd)
  have hleft : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp n v x) z) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hright : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp n v x) z) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hL := integral_map (μ := gaussianCoordinates) hleft.aemeasurable hF.aestronglyMeasurable
  have hR := integral_map (μ := gaussianCoordinates) hright.aemeasurable hF.aestronglyMeasurable
  rw [tensorNamespacedFields_law] at hL
  exact hL.symm.trans hR


lemma measurable_tensorFlat_replicaMean {N m k r : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (D : (Fin r → Spin N × LabeledLeaf n) → ℝ) :
    Measurable (fun p : LabeledTree n × (ℕ → ℝ) =>
      referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
        (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
          cylinderField (tensorLeafCoefficients U I degree amp n v x) p.2) D) := by
  let ν : LabeledTree n × (ℕ → ℝ) → Measure (Spin N × LabeledLeaf n) := fun p =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1
  let H : (LabeledTree n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) → ℝ := fun p =>
    rotatedEnergy eig U p.2.1 + fieldEnergy c p.2.1 +
      cylinderField (tensorLeafCoefficients U I degree amp n v p.2) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) p.1))
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst
  have hH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro x
    change Measurable (fun p : LabeledTree n × (ℕ → ℝ) =>
      (rotatedEnergy eig U x.1 + fieldEnergy c x.1) +
        cylinderField (tensorLeafCoefficients U I degree amp n v x) p.2)
    exact (show Measurable (fun _ : LabeledTree n × (ℕ → ℝ) =>
      rotatedEnergy eig U x.1 + fieldEnergy c x.1) from
      measurable_const).add ((measurable_cylinderField
        (tensorLeafCoefficients U I degree amp n v x)).comp measurable_snd)
  have hD : Measurable (fun p : (LabeledTree n × (ℕ → ℝ)) ×
      (Fin r → Spin N × LabeledLeaf n) => D p.2) :=
    (measurable_of_countable D).comp measurable_snd
  exact measurable_random_referenceReplicaMean hν hH hD


lemma tensorNamespacedReplicaAverage_leafPrefix {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hb : CascadeExponents n b) (hh : Monotone h) (h0 : 0 ≤ h 0) (d : Fin n) :
    tensorNamespacedReplicaAverage μ eig c I degree amp n b r h
      (fun _ => tensorLeafPrefixTest d) = 1 - b d := by
  let D := tensorLeafPrefixTest (N := N) d
  let ν := fun p : TensorFlatDisorder N n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let F := fun p : TensorFlatDisorder N n => referenceReplicaMean (ν p)
    (tensorNamespacedHamiltonian eig c I degree amp n r h p) D
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) p.1.2))
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.snd
  have hF : Measurable F := measurable_random_referenceReplicaMean hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n r h)
    ((measurable_of_countable D).comp measurable_snd)
  have hFb p : |F p| ≤ 1 := referenceReplicaMean_abs_le _ _ _
    (measurable_of_countable D) zero_le_one (tensorLeafPrefixTest_abs_le d)
  have hFi : Integrable F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
      gaussianCoordinates) := integrable_of_measurable_abs_le hF hFb
  calc
    _ = ∫ p, F p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
        gaussianCoordinates := by
      unfold tensorNamespacedReplicaAverage
      apply integral_congr_ae
      filter_upwards [tensorNamespaced_exp_integrable_ae μ eig c I degree amp n b r h hh h0]
        with p hp
      exact referenceReplicaMean_gibbsProbability (ν p)
        (tensorNamespacedHamiltonian eig c I degree amp n r h p) hp D
    _ = ∫ p, ∫ z, F (p,z) ∂gaussianCoordinates
        ∂μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n)) := integral_prod _ hFi
    _ = ∫ U, ∫ T, ∫ z, F ((U,T),z) ∂gaussianCoordinates
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) ∂μ :=
      integral_prod _ hFi.integral_prod_left
    _ = ∫ _U, 1 - b d ∂μ := by
      apply integral_congr_ae
      refine ae_of_all _ fun U => ?_
      let v := tensorPathProfile I degree n r h
      let G := fun p : LabeledTree n × (ℕ → ℝ) =>
        referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
          (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1 +
            cylinderField (tensorLeafCoefficients (specialRotation U) I degree amp n (fun i => v i) x) p.2) D
      have hG : Measurable G := measurable_tensorFlat_replicaMean eig
        (specialRotation U) c I degree amp n (fun i => v i) D
      have hGi : Integrable G ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
          gaussianCoordinates) := integrable_of_measurable_abs_le hG (fun _ =>
        referenceReplicaMean_abs_le _ _ D (measurable_of_countable D) zero_le_one
          (tensorLeafPrefixTest_abs_le d))
      calc
        _ = ∫ T, ∫ z, G (T,z) ∂gaussianCoordinates
            ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
          apply integral_congr_ae
          refine ae_of_all _ fun T => ?_
          exact (tensorGaussian_replicaMean_namespace eig (specialRotation U) c I degree amp
            n T (fun i => v i) D).symm
        _ = ∫ p, G p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates :=
          (integral_prod _ hGi).symm
        _ = 1 - b d := tensorFlat_leafPrefix_mean hN eig (specialRotation U) c I degree amp n b v hb d
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
