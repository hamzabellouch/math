import OAI.Probability.InvariantIsing.Fields.SpinPriorReplicaAverage
import OAI.Probability.InvariantIsing.Fields.SpinPriorExponential
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage

namespace OAI

/-! Exact quenched cascade mixture for an arbitrary constrained spin prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

 theorem spinPriorReplicaAverage_cascade_mixture {N m k r : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0)
    (D : SpecialOrthogonal N → (Fin r → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : 0 ≤ B)
    (hDB : ∀ U σ, |D U σ| ≤ B) :
    spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h D =
      ∫ T, ∫ z : SpecialOrthogonal N × (ℕ → ℝ),
        referenceReplicaMean (labeledSpinReference n π T)
          (tensorRestrictionHamiltonian eig c I degree amp
            (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2) (D z.1)
          ∂μ.prod gaussianCoordinates ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  let F := fun p : TensorFlatDisorder N n =>
    referenceReplicaMean (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h p)
      (fun _ => 0) (D p.1.1)
  let S := fun q : LabeledTree n × (SpecialOrthogonal N × (ℕ → ℝ)) => ((q.2.1,q.1),q.2.2)
  have hS := tensorCascadeDisorderShuffle_preserving μ (n := n) b
  have hmF : Measurable F := measurable_spinPriorReplicaMean π eig c I degree amp n treeDegree h D hD
  have hiF : Integrable (F ∘ S)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (μ.prod gaussianCoordinates)) := by
    apply integrable_of_measurable_abs_le (hmF.comp hS.measurable)
    intro q
    change |referenceReplicaMean (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h (S q))
      (fun _ => 0) (D q.2.1)| ≤ B
    exact referenceReplicaMean_abs_le _ _ _ (measurable_of_countable (D q.2.1)) hB (hDB q.2.1)
  unfold spinPriorReplicaAverage
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
        (labeledSpinReference n π T)
        eig c I degree amp treeDegree h hh h0 (id : Spin N × LabeledLeaf n → _)
      apply integral_congr_ae
      filter_upwards [he] with z hz
      dsimp only [F, S]
      change referenceReplicaMean (gibbsProbability (labeledSpinReference n π T)
        (tensorRestrictionHamiltonian eig c I degree amp
          (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2))
        (fun _ => 0) (D z.1) = _
      exact referenceReplicaMean_gibbsProbability _ _ hz _

end InvariantIsing

end

end OAI
