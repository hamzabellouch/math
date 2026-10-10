import OAI.Probability.InvariantIsing.Arrays.NSpinTensorGaussianLaw
import OAI.Probability.InvariantIsing.Fields.PriorFieldLogNormalizer

namespace OAI

/-! Conditional cascade moments for the actual tensor field with an arbitrary
probability spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorCascadeValue {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  energyRecursion n b (fun i => tensorEnergyMarkLaw U I degree amp (v i)) π
    (tensorSpinBaseEnergy eig U c I degree amp z)

def spinPriorLabeledLog {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorLabeledData N n) : ℝ :=
  Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amp n z p x)
    ∂labeledSpinReference n π p.1)

lemma measurable_spinPriorCascadeValue {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (spinPriorCascadeValue π eig U c I degree amp n b v) := by
  apply (measurable_energyRecursion n b _ π).comp
  unfold tensorSpinBaseEnergy spinTensorEnergy
  fun_prop

lemma measurable_spinPriorLabeledLog_root {N m k : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (n : ℕ) :
    Measurable (fun q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
      spinPriorLabeledLog π eig U c I degree amp n q.1 q.2) := by
  have : ∀ q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n,
      IsProbabilityMeasure ((labeledSpinReference n π ∘ fun q => q.2.1) q) := fun q => by
        change IsProbabilityMeasure (labeledSpinReference n π q.2.1)
        infer_instance
  exact (measurable_random_referencePartition
    ((measurable_labeledSpinReference_general n π).comp measurable_snd.fst)
    (measurable_tensorLabeledEnergy_root eig U c I degree amp n)).log

theorem spinPriorLabeledLog_conditional {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    let P := tensorLabeledLaw U I degree amp n b v
    let F := spinPriorLabeledLog π eig U c I degree amp n z
    let X := spinPriorCascadeValue π eig U c I degree amp n b v z
    Integrable F P ∧ (∫ p, F p ∂P) = X ∧
      Integrable (fun p => (F p-X)^2) P ∧
      (∫ p, (F p-X)^2 ∂P) ≤
        4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2
          ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  intro P F X
  let μ := fun i => tensorEnergyMarkLaw U I degree amp (v i)
  let H := tensorSpinBaseEnergy eig U c I degree amp z
  let J := fun p : TensorLabeledData N n =>
    labeledNoiseJoin (Spin N → ℝ) n (p.1, markForestOfCoords (Spin N → ℝ) n p.2)
  have hp : MeasurePreserving J P (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure _) :=
    (show MeasurePreserving (labeledNoiseJoin (Spin N → ℝ) n)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (Spin N → ℝ) n μ))
      (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure _) from
        ⟨measurable_labeledNoiseJoin _ _, labeledNoiseJoin_law _ _ _ _⟩).comp
      (cascadeCoordinates_preserving n b μ)
  have he0 := (cascadeCoordinates_preserving n b μ).quasiMeasurePreserving.ae
    (labeledEnergyLog_eq_cascade n b hb μ π H)
  have he : F =ᵐ[P] fun p => cascadeEnergyLog n b μ π H (J p) := by
    filter_upwards [he0] with p hpe
    simpa only [F, spinPriorLabeledLog, tensorLabeledEnergy, cascadeCoordinateEnergy_eq, labeledEnergyLog] using hpe
  have hc := cascadeEnergyLog_conditional n b hb μ π
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amp (v i)) H
  have hs : (fun p => (F p-X)^2) =ᵐ[P]
      fun p => (cascadeEnergyLog n b μ π H (J p)-X)^2 := he.fun_comp (fun x => (x-X)^2)
  refine ⟨(hp.integrable_comp_of_integrable hc.1).congr he.symm, ?_,
    (hp.integrable_comp_of_integrable hc.2.2.1).congr hs.symm, ?_⟩
  · rw [integral_congr_ae he]
    exact (integral_comp_preserving_ae hp hc.1.aestronglyMeasurable).trans hc.2.1
  · rw [integral_congr_ae hs]
    change (∫ p, (cascadeEnergyLog n b μ π H (J p)-energyRecursion n b μ π H)^2 ∂P) ≤ _
    rw [integral_comp_preserving_ae hp hc.2.2.1.aestronglyMeasurable]
    exact hc.2.2.2

end InvariantIsing

end

end OAI
