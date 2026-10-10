import OAI.Probability.InvariantIsing.Arrays.TensorCountableHamiltonian
import OAI.Probability.InvariantIsing.Arrays.TensorReplicaAverageLaw

namespace OAI

/-! The actual enriched replica average is a cascade mixture of fixed-prior
spin/leaf averages. The common rotation is retained in the mixture. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma referenceReplicaMean_gibbsProbability {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean (gibbsProbability ν H) (fun _ => 0) D = referenceReplicaMean ν H D := by
  rw [referenceReplicaMean_zero, gibbsProbability_eq_tilted ν H he,
    referenceReplicaMean_eq_tilted ν H he]

lemma tensorCascadeDisorderShuffle_preserving {N n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (b : ℕ → ℝ) :
    MeasurePreserving
      (fun q : LabeledTree n × (SpecialOrthogonal N × (ℕ → ℝ)) => ((q.2.1,q.1),q.2.2))
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (μ.prod gaussianCoordinates))
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  have hp := ((Measure.measurePreserving_swap (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := μ)).prod (MeasurePreserving.id gaussianCoordinates)).comp
      ((measurePreserving_prodAssoc (labeledCascadeLaw n b : Measure (LabeledTree n)) μ
        gaussianCoordinates).symm MeasurableEquiv.prodAssoc)
  convert hp using 1
  funext q
  rfl

lemma tensorRestrictionHamiltonian_id_eq {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (T : LabeledTree n)
    (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    tensorRestrictionHamiltonian eig c I degree amp
      (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2 =
      tensorNamespacedHamiltonian eig c I degree amp n treeDegree h ((z.1,T),z.2) := rfl

 theorem tensorNamespacedReplicaAverage_cascade_mixture {N m k r : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0)
    (D : SpecialOrthogonal N → (Fin r → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : 0 ≤ B)
    (hDB : ∀ U σ, |D U σ| ≤ B) :
    tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h D =
      ∫ T, ∫ z : SpecialOrthogonal N × (ℕ → ℝ),
        referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
          (tensorRestrictionHamiltonian eig c I degree amp
            (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2) (D z.1)
          ∂μ.prod gaussianCoordinates ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  let F := fun p : TensorFlatDisorder N n =>
    referenceReplicaMean (tensorNamespacedReference eig c I degree amp n treeDegree h p)
      (fun _ => 0) (D p.1.1)
  let S := fun q : LabeledTree n × (SpecialOrthogonal N × (ℕ → ℝ)) => ((q.2.1,q.1),q.2.2)
  have hS := tensorCascadeDisorderShuffle_preserving μ (n := n) b
  have hmF : Measurable F := measurable_tensorNamespacedReplicaMean eig c I degree amp n treeDegree h D hD
  have hiF : Integrable (F ∘ S)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (μ.prod gaussianCoordinates)) := by
    apply integrable_of_measurable_abs_le (hmF.comp hS.measurable)
    intro q
    change |referenceReplicaMean (tensorNamespacedReference eig c I degree amp n treeDegree h (S q))
      (fun _ => 0) (D q.2.1)| ≤ B
    exact referenceReplicaMean_abs_le _ _ _ (measurable_of_countable (D q.2.1)) hB (hDB q.2.1)
  unfold tensorNamespacedReplicaAverage
  change (∫ p, F p ∂_) = _
  calc
    _ = ∫ q, F (S q) ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (μ.prod gaussianCoordinates) := (hS.hasLaw.integral_comp hmF.aestronglyMeasurable).symm
    _ = ∫ T, ∫ z, F (S (T,z)) ∂μ.prod gaussianCoordinates
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := integral_prod _ hiF
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun T => ?_
      have he := tensorCountableHamiltonian_exp_integrable_ae μ
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
        eig c I degree amp treeDegree h hh h0 (id : Spin N × LabeledLeaf n → _)
      apply integral_congr_ae
      filter_upwards [he] with z hz
      dsimp only [F, S]
      unfold tensorNamespacedReference
      rw [← tensorRestrictionHamiltonian_id_eq eig c I degree amp treeDegree h T z]
      exact referenceReplicaMean_gibbsProbability _ _ hz _

end InvariantIsing

end

end OAI
