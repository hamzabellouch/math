import OAI.Probability.InvariantIsing.Pressure.GibbsMap
import OAI.Probability.InvariantIsing.Arrays.TensorSeedReplicaTransport
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorPairConditioning

namespace OAI

/-! The actual tensor terminal Gibbs law on the countable labeled leaf space. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma tensorLeafState_labeled {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (α : LabeledLeaf n) :
    tensorLeafState I degree n z (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
      (p.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α) =
      labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    exact ih (z + p.2 (α.1.1,α.1.2,none))
      (p.1.2 α.1.1 α.1.2,fun v => p.2 (α.1.1,α.1.2,some v)) α.2

def tensorLabeledTerminalGibbs {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n) :
    Measure (LabeledLeaf n) :=
  gibbsProbability (labeledLeafLaw n p.1) (fun α => spinTensorTerminal eig U c I degree amplitude
    (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z))

instance tensorLabeledTerminalGibbs_probability {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n) :
    IsProbabilityMeasure (tensorLabeledTerminalGibbs eig U c I degree amplitude n z p) := by
  unfold tensorLabeledTerminalGibbs
  infer_instance

lemma measurable_tensorLabeledTerminalGibbs {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    Measurable (tensorLabeledTerminalGibbs eig U c I degree amplitude n z) := by
  unfold tensorLabeledTerminalGibbs
  apply measurable_gibbsProbability (ν := fun p : TensorCoordinateData I degree n => labeledLeafLaw n p.1)
    (H := fun p : TensorCoordinateData I degree n × LabeledLeaf n =>
      spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) p.2 z))
    ((measurable_labeledLeafLaw n).comp measurable_fst)
  apply measurable_from_prod_countable_left
  intro α
  exact (measurable_spinTensorTerminal eig U c I degree amplitude).comp
    ((measurable_labeledEnergy n α).comp
      (((measurable_markForestOfCoords _ n).comp measurable_snd).prodMk measurable_const))

lemma tensorLabeledTerminal_exp_integrable_ae {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ p ∂tensorCoordinateLaw I degree n b v,
      Integrable (fun α => Real.exp (spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1) := by
  filter_upwards [tensorLeafSpin_exp_integrable_ae hN eig U c I degree amplitude n b v hb z] with p hp
  convert spinLeafTerminal_exp_integrable (labeledLeafLaw n p.1)
    (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) hp using 1
  simp only [spinLeafTerminal_tensorLeafSpinHamiltonian]

end InvariantIsing

end

end OAI
