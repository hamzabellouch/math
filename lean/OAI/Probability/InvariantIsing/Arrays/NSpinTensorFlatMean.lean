import OAI.Probability.InvariantIsing.Arrays.NSpinTensorGaussianLaw
import OAI.Probability.InvariantIsing.Gaussian.BaseGaussianVariance
import OAI.Probability.IsingPerceptron.NamespaceSplit

namespace OAI

/-! The flat Gaussian spin/leaf pressure has the actual cascade mean. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorFlatLog {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp (rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
    cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)

lemma measurable_tensorFlatLog {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (tensorFlatLog eig U c I degree amplitude n v) := by
  have hE : Measurable (fun p : (LabeledTree n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig U p.2.1 + fieldEnergy c p.2.1 +
        cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hc : Measurable (fun _ : LabeledTree n × (ℕ → ℝ) =>
        rotatedEnergy eig U x.1 + fieldEnergy c x.1) := measurable_const
    exact hc.add ((measurable_cylinderField
      (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x)).comp measurable_snd)
  have : ∀ p : LabeledTree n × (ℕ → ℝ), IsProbabilityMeasure
      ((labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ∘ Prod.fst) p) :=
    fun p => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
      infer_instance
  exact (measurable_random_referencePartition
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst) hE).log

private lemma tensorLeafCoefficients_finite_bound {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    ∃ B : ℝ, ∀ x : Spin N × LabeledLeaf n,
      (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x).sum (fun _ c => c ^ 2) ≤ B := by
  classical
  let Q : Spin N → ℝ := fun σ => ∑ i : Fin (n + 1), ∑ j : SpinTensorIndex I degree,
    (v i j : ℝ) * spinTensorFeature U I degree amplitude σ j ^ 2
  refine ⟨∑ σ, Q σ, fun x => ?_⟩
  rw [← cylinderCross_self, tensorLeafCoefficients_cross]
  simp only [labeledCommonDepth_self,
    show ∀ i : Fin (n + 1), i.1 ≤ n from fun i => Nat.le_of_lt_succ i.isLt, ite_true]
  calc
    _ = Q x.1 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ σ, Q σ := Finset.single_le_sum (f := Q)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)) (Finset.mem_univ x.1)

private lemma tensorFlat_base_exp_integrable {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (n : ℕ) (T : LabeledTree n) :
    Integrable (fun x : Spin N × LabeledLeaf n => Real.exp (rotatedEnergy eig U x.1 + fieldEnergy c x.1))
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T) :=
  (Integrable.of_finite : Integrable
    (fun σ : Spin N => Real.exp (rotatedEnergy eig U σ + fieldEnergy c σ))
    (uniformSpinPrior N : Measure (Spin N))).comp_fst (labeledLeafLaw n T)

private lemma tensorFlat_base_log {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (n : ℕ) (T : LabeledTree n) :
    Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp (rotatedEnergy eig U x.1 + fieldEnergy c x.1)
      ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T) =
      logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) := by
  unfold labeledSpinReference
  change Real.log (∫ x : Spin N × LabeledLeaf n,
    (fun σ : Spin N => Real.exp (rotatedEnergy eig U σ + fieldEnergy c σ)) x.1
    ∂(uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n T)) = _
  rw [integral_fun_fst (μ := (uniformSpinPrior N : Measure (Spin N)))
    (ν := labeledLeafLaw n T) (fun σ : Spin N => Real.exp (rotatedEnergy eig U σ + fieldEnergy c σ))]
  simp only [probReal_univ, one_smul]
  exact finiteLogIntegral_uniformSpinPrior _

private lemma random_cylinder_log_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : X → ℝ) (hH : ∀ ω, Integrable (fun x => Real.exp (H x)) (ν ω))
    (C : ℝ) (hC : ∀ ω, Real.log (∫ x, Real.exp (H x) ∂ν ω) = C)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    Integrable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) p.2) ∂ν p.1)) (P.prod gaussianCoordinates) := by
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted H) := fun ω => isProbabilityMeasure_tilted (hH ω)
  have hHH : Measurable (fun p : Ω × X => H p.2) :=
    (measurable_of_countable H).comp measurable_snd
  have htilt : Measurable (fun ω => (ν ω).tilted H) :=
    measurable_random_tilted_measure (H := fun p : Ω × X => H p.2) hν hHH
  let G := fun p : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A x) p.2) ((ν p.1).tilted H) 1
  have hmG : Measurable G := measurable_random_cylinder_cgf htilt A 1
  have hiG : Integrable G (P.prod gaussianCoordinates) := integrable_random_cylinder_cgf htilt A hA 1
  have : ∀ p : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun p : Ω × (ℕ → ℝ) => ν p.1) p) :=
    fun p => by change IsProbabilityMeasure (ν p.1); infer_instance
  have hE : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => H p.2 + cylinderField (A p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hc : Measurable (fun _ : Ω × (ℕ → ℝ) => H x) := measurable_const
    exact hc.add ((measurable_cylinderField (A x)).comp measurable_snd)
  have hm : Measurable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) p.2) ∂ν p.1)) :=
    (measurable_random_referencePartition (ν := fun p : Ω × (ℕ → ℝ) => ν p.1)
      (hν.comp measurable_fst) hE).log
  have heq : (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) p.2) ∂ν p.1)) =ᵐ[P.prod gaussianCoordinates]
      (fun p => C + G p) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm (measurable_const.add hmG))).mpr
    exact ae_of_all _ fun ω => by
      have he := cylinder_log_partition_base (ν ω) H (hH ω) A hA 1
      filter_upwards [he] with g hg
      dsimp only [G, Pi.add_apply]
      simpa only [one_mul, hC ω] using hg
  exact ((integrable_const C).add hiG).congr (Filter.EventuallyEq.symm heq)

/-- Joint integrability over the actual cascade branching and flat
Gaussian coordinates, without a variance or pressure-limit hypothesis. -/
theorem tensorFlatLog_integrable {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Integrable (tensorFlatLog eig U c I degree amplitude n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) := by
  let ν := fun T : LabeledTree n => labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  have : ∀ T, IsProbabilityMeasure (ν T) := fun T => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
    infer_instance
  obtain ⟨B, hcap⟩ := tensorLeafCoefficients_finite_bound U I degree amplitude n v
  exact random_cylinder_log_integrable
    (ν := ν) (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N)))
    (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1)
    (tensorFlat_base_exp_integrable eig U c n)
    (logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ))
    (tensorFlat_base_log eig U c n)
    (tensorLeafCoefficients U I degree amplitude n (fun i => v i)) hcap

/-- The flat spin/leaf log partition has exactly the same mean as the
root-averaged tensor cascade recursion. -/
theorem tensorFlatLog_mean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    (∫ p, tensorFlatLog eig U c I degree amplitude n v p
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
      ∫ z, tensorCascadeValue eig U c I degree amplitude n b (fun i => v (i + 1)) z
        ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) := by
  let G := fun q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n q.1 q.2 x)
      ∂tensorLabeledReference N n q.2)
  have : ∀ q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n,
      IsProbabilityMeasure ((tensorLabeledReference N n ∘ Prod.snd) q) := fun q => by
        change IsProbabilityMeasure (tensorLabeledReference N n q.2)
        infer_instance
  have hmG : Measurable G := (measurable_random_referencePartition
    ((measurable_tensorLabeledReference N n).comp measurable_snd)
    (measurable_tensorLabeledEnergy_root eig U c I degree amplitude n)).log
  have hp := tensorFlatToLabeled_measurePreserving U I degree amplitude n b v
  have he : G ∘ tensorFlatToLabeled U I degree amplitude n v =
      tensorFlatLog eig U c I degree amplitude n v := by
    funext p
    apply congrArg Real.log
    change (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n
      (tensorFlatToLabeled U I degree amplitude n v p).1
      (tensorFlatToLabeled U I degree amplitude n v p).2 x)
      ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1) = _
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    exact congrArg Real.exp (tensorLabeledEnergy_flat_eq eig U c I degree amplitude n v p x)
  have hi : Integrable (G ∘ tensorFlatToLabeled U I degree amplitude n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) := by
    rw [he]
    exact tensorFlatLog_integrable eig U c I degree amplitude n b v
  have hiG : Integrable G
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorLabeledLaw U I degree amplitude n b (fun i => v (i + 1)))) := by
    rw [← hp.map_eq]
    exact (integrable_map_measure hmG.aestronglyMeasurable hp.aemeasurable).mpr hi
  rw [← he]
  change (∫ p, G (tensorFlatToLabeled U I degree amplitude n v p)
    ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) = _
  rw [integral_comp_preserving_ae hp hmG.aestronglyMeasurable, integral_prod _ hiG]
  apply integral_congr_ae
  exact ae_of_all _ fun z =>
    (tensorLabeledLog_mean hN eig U c I degree amplitude n b (fun i => v (i + 1)) hb z).2

theorem tensorEnrichedPressure_eq_flat_mean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    tensorEnrichedPressure eig U c I degree amplitude n b (fun i => v (i + 1)) (v 0) =
      (N : ℝ)⁻¹ * ∫ T, (∫ g : ℕ → ℝ, tensorFlatLog eig U c I degree amplitude n v (T, g)
        ∂gaussianCoordinates) ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  rw [tensorEnrichedPressure, ← tensorFlatLog_mean hN eig U c I degree amplitude n b v hb,
    integral_prod _ (tensorFlatLog_integrable eig U c I degree amplitude n b v)]

end InvariantIsing

end

end OAI
