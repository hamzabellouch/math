import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFluctuation
import OAI.Probability.IsingPerceptron.TiltedLabelLaw

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def uniformSpinPrior (N : ℕ) : ProbabilityMeasure (Spin N) :=
  ⟨(PMF.uniformOfFintype (Spin N)).toMeasure, inferInstance⟩

lemma finiteLogIntegral_uniformSpinPrior {N : ℕ} (H : Spin N → ℝ) :
    IsingPerceptron.finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) H = logPartition H := by
  unfold IsingPerceptron.finiteLogIntegral logPartition
  congr 1
  change (∫ σ, Real.exp (H σ) ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]

lemma measurable_spinTensorEnergyMark {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    Measurable (fun z : SpinTensorIndex I degree → ℝ =>
      spinTensorEnergy U I degree amplitude z) := by
  unfold spinTensorEnergy
  fun_prop

def tensorEnergyMarkLaw {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : SpinTensorIndex I degree → ℝ≥0) : ProbabilityMeasure (Spin N → ℝ) :=
  (tensorGaussianLaw I degree v).map (fun z => spinTensorEnergy U I degree amplitude z)

lemma spinTensorEnergyMark_norm_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) :
    ‖spinTensorEnergy U I degree amplitude z‖ ≤
      (∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
        |spinTensorFeature U I degree amplitude σ i|) * ‖z‖ := by
  classical
  let L : ℝ := ∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
    |spinTensorFeature U I degree amplitude σ i|
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg z))).mpr
  intro σ
  rw [Real.norm_eq_abs]
  have hσ : (∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude σ i|) ≤ L := by
    apply Finset.single_le_sum (f := fun τ : Spin N =>
      ∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude τ i|)
    · exact fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.mem_univ σ
  calc
    _ ≤ ∑ i, |z i * spinTensorFeature U I degree amplitude σ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖z‖ * |spinTensorFeature U I degree amplitude σ i| :=
      Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
          (abs_nonneg _)
    _ = ‖z‖ * ∑ i, |spinTensorFeature U I degree amplitude σ i| := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖z‖ * L := mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
    _ = _ := mul_comm _ _

lemma tensorEnergyMarkLaw_moments {N m k : ℕ} (hN : 0 < N) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments (tensorEnergyMarkLaw U I degree amplitude v :
      Measure (Spin N → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop)
    (measurable_spinTensorEnergyMark U I degree amplitude).aemeasurable).mpr
  let L : ℝ := ∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
    |spinTensorFeature U I degree amplitude σ i|
  have hi := tensorGaussianLaw_moments hN I degree v (|a| * L)
  apply hi.mono' (((measurable_spinTensorEnergyMark U I degree amplitude).norm.const_mul a).exp.aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      a * ‖spinTensorEnergy U I degree amplitude z‖ ≤ |a| * ‖spinTensorEnergy U I degree amplitude z‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |a| * (L * ‖z‖) := mul_le_mul_of_nonneg_left
        (spinTensorEnergyMark_norm_le U I degree amplitude z) (abs_nonneg _)
      _ = _ := by ring

def tensorSpinBaseEnergy {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) : Spin N → ℝ :=
  fun σ => rotatedEnergy eig U σ + fieldEnergy c σ + spinTensorEnergy U I degree amplitude z σ

lemma tensorSpinBaseEnergy_add {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z a : SpinTensorIndex I degree → ℝ) :
    tensorSpinBaseEnergy eig U c I degree amplitude (z + a) =
      tensorSpinBaseEnergy eig U c I degree amplitude z + spinTensorEnergy U I degree amplitude a := by
  ext σ
  simp only [tensorSpinBaseEnergy, Pi.add_apply, spinTensorEnergy_add]
  ring

/-- Pushforward of the Gaussian energy marks commutes with the actual
backward recursion. The terminal keeps the uniform probability Ising prior. -/
theorem tensorCascadeValue_eq_energyRecursion {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) :
    tensorCascadeValue eig U c I degree amplitude n b v z =
      IsingPerceptron.energyRecursion n b (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))
        (uniformSpinPrior N : Measure (Spin N)) (tensorSpinBaseEnergy eig U c I degree amplitude z) := by
  induction n generalizing b v z with
  | zero => exact (finiteLogIntegral_uniformSpinPrior _).symm
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let G := IsingPerceptron.energyRecursion n bs
      (fun i => tensorEnergyMarkLaw U I degree amplitude (vs i)) (uniformSpinPrior N : Measure (Spin N))
    have hmG : Measurable G := IsingPerceptron.measurable_energyRecursion _ _ _ _
    change Real.log (∫ a, Real.exp (b 0 * tensorCascadeValue eig U c I degree amplitude n bs vs (z + a))
        ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))) / b 0 =
      Real.log (∫ a, Real.exp (b 0 * G (tensorSpinBaseEnergy eig U c I degree amplitude z + a))
        ∂(tensorEnergyMarkLaw U I degree amplitude (v 0) : Measure (Spin N → ℝ))) / b 0
    congr 2
    have hme : Measurable (fun a : Spin N → ℝ =>
        Real.exp (b 0 * G (tensorSpinBaseEnergy eig U c I degree amplitude z + a))) :=
      ((hmG.comp (measurable_const.add measurable_id)).const_mul (b 0)).exp
    have hmap := integral_map (μ := (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)))
      (measurable_spinTensorEnergyMark U I degree amplitude).aemeasurable hme.aestronglyMeasurable
    change (∫ a, Real.exp (b 0 * G (tensorSpinBaseEnergy eig U c I degree amplitude z + a))
      ∂(tensorEnergyMarkLaw U I degree amplitude (v 0) : Measure (Spin N → ℝ))) = _ at hmap
    rw [hmap]
    apply integral_congr_ae
    refine ae_of_all _ fun a => ?_
    dsimp only
    rw [ih bs vs (z + a), tensorSpinBaseEnergy_add]

abbrev TensorLabeledData (N n : ℕ) :=
  IsingPerceptron.LabeledTree n × (IsingPerceptron.ForestVertex n → Spin N → ℝ)

abbrev TensorLabeledState (N n : ℕ) := Spin N × IsingPerceptron.LabeledLeaf n

def tensorLabeledLaw {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) : Measure (TensorLabeledData N n) :=
  IsingPerceptron.cascadeCoordinateLaw n b (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))

abbrev TensorCoordinateData {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :=
  IsingPerceptron.LabeledTree n × (IsingPerceptron.ForestVertex n → SpinTensorIndex I degree → ℝ)

def tensorCoordinateLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) : Measure (TensorCoordinateData I degree n) :=
  (IsingPerceptron.labeledCascadeLaw n b : Measure (IsingPerceptron.LabeledTree n)).prod
    (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
      (tensorGaussianLaw I degree (v (IsingPerceptron.forestVertexDepth n w)) :
        Measure (SpinTensorIndex I degree → ℝ))))

instance tensorCoordinateLaw_probability {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorCoordinateLaw I degree n b v) := by
  unfold tensorCoordinateLaw
  infer_instance

def tensorEnergyCoordinates {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorCoordinateData I degree n) : TensorLabeledData N n :=
  (p.1, fun w => spinTensorEnergy U I degree amplitude (p.2 w))

lemma measurable_tensorEnergyCoordinates_joint {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × TensorCoordinateData I degree n =>
      tensorEnergyCoordinates (specialRotation p.1) I degree amplitude n p.2) := by
  refine measurable_snd.fst.prodMk (Measurable.of_eval fun w => Measurable.of_eval fun σ => ?_)
  apply Finset.measurable_sum
  intro i _
  have hc : Measurable (fun p : SpecialOrthogonal N × TensorCoordinateData I degree n => p.2.2 w i) := by
    fun_prop
  exact hc.mul ((measurable_spinTensorFeature I degree amplitude σ i).comp measurable_fst)

theorem tensorEnergyCoordinates_measurePreserving {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorEnergyCoordinates U I degree amplitude n)
      (tensorCoordinateLaw I degree n b v) (tensorLabeledLaw U I degree amplitude n b v) := by
  have hmark : MeasurePreserving
      (fun z : IsingPerceptron.ForestVertex n → SpinTensorIndex I degree → ℝ =>
        fun w => spinTensorEnergy U I degree amplitude (z w))
      (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
        (tensorGaussianLaw I degree (v (IsingPerceptron.forestVertexDepth n w)) :
          Measure (SpinTensorIndex I degree → ℝ))))
      (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
        (tensorEnergyMarkLaw U I degree amplitude (v (IsingPerceptron.forestVertexDepth n w)) :
          Measure (Spin N → ℝ)))) := by
    refine ⟨Measurable.of_eval (fun w =>
      (measurable_spinTensorEnergyMark U I degree amplitude).comp (measurable_pi_apply w)), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_spinTensorEnergyMark U I degree amplitude)]
    rfl
  convert (MeasurePreserving.id (IsingPerceptron.labeledCascadeLaw n b :
    Measure (IsingPerceptron.LabeledTree n))).prod hmark using 1
  all_goals rfl

instance tensorLabeledLaw_probability {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorLabeledLaw U I degree amplitude n b v) := by
  unfold tensorLabeledLaw
  infer_instance

def tensorLabeledReference (N n : ℕ) (p : TensorLabeledData N n) : Measure (TensorLabeledState N n) :=
  IsingPerceptron.labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1

instance tensorLabeledReference_probability (N n : ℕ) (p : TensorLabeledData N n) :
    IsProbabilityMeasure (tensorLabeledReference N n p) := by
  unfold tensorLabeledReference
  infer_instance

lemma measurable_tensorLabeledReference (N n : ℕ) : Measurable (tensorLabeledReference N n) :=
  (IsingPerceptron.measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst

def tensorLabeledEnergy {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorLabeledData N n) : TensorLabeledState N n → ℝ :=
  IsingPerceptron.cascadeCoordinateEnergy n (tensorSpinBaseEnergy eig U c I degree amplitude z) p

lemma measurable_tensorLabeledEnergy {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    Measurable (fun p : TensorLabeledData N n × TensorLabeledState N n =>
      tensorLabeledEnergy eig U c I degree amplitude n z p.1 p.2) :=
  IsingPerceptron.measurable_cascadeCoordinateEnergy n _

lemma measurable_tensorLabeledEnergy_root {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) :
    Measurable (fun p : ((SpinTensorIndex I degree → ℝ) × TensorLabeledData N n) ×
        TensorLabeledState N n => tensorLabeledEnergy eig U c I degree amplitude n p.1.1 p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  change Measurable (fun p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    tensorSpinBaseEnergy eig U c I degree amplitude p.1 s.1 +
      ∑ i : Fin n, p.2.2 (IsingPerceptron.edgeAt n s.2 i) s.1)
  unfold tensorSpinBaseEnergy spinTensorEnergy
  fun_prop

theorem tensorLabeled_exp_integrable {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ p ∂tensorLabeledLaw U I degree amplitude n b v,
      Integrable (fun s => Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z p s))
        (tensorLabeledReference N n p) :=
  IsingPerceptron.cascadeCoordinate_exp_integrable n b hb
    (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))
    (uniformSpinPrior N : Measure (Spin N))
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amplitude (v i)) _

theorem tensorLabeledLog_mean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    let F := fun p => Real.log (∫ s, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z p s)
      ∂tensorLabeledReference N n p)
    Integrable F (tensorLabeledLaw U I degree amplitude n b v) ∧
      (∫ p, F p ∂tensorLabeledLaw U I degree amplitude n b v) =
        tensorCascadeValue eig U c I degree amplitude n b v z := by
  have h := IsingPerceptron.cascadeCoordinate_log_integral n b hb
    (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))
    (uniformSpinPrior N : Measure (Spin N))
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amplitude (v i))
    (tensorSpinBaseEnergy eig U c I degree amplitude z)
  exact ⟨h.1, h.2.trans (tensorCascadeValue_eq_energyRecursion eig U c I degree amplitude n b v z).symm⟩

/-- The exact parent-prefix probability of two tilted replicas is the
original cascade marginal, for the concrete tensor-enriched Ising model. -/
theorem tensorLabeled_tilted_parent_tail {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) (d : Fin n) :
    (∫ p, IsingPerceptron.referenceReplicaMean (tensorLabeledReference N n p)
      (tensorLabeledEnergy eig U c I degree amplitude n z p)
      (fun σ : Fin 2 → TensorLabeledState N n =>
        if (IsingPerceptron.labeledAddress n (σ 1).2).take (d + 1) =
          (IsingPerceptron.labeledAddress n (σ 0).2).take (d + 1) then 1 else 0)
      ∂tensorLabeledLaw U I degree amplitude n b v) = 1 - b d :=
  IsingPerceptron.cascadeCoordinate_tilted_label_tail n b hb
    (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))
    (uniformSpinPrior N : Measure (Spin N))
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amplitude (v i)) _ d

end InvariantIsing

end

end OAI
