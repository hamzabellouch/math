import OAI.Probability.InvariantIsing.Arrays.TensorRetainedSeedLaw
import OAI.Probability.InvariantIsing.Fields.CascadeSeedReplicaLaw

namespace OAI

/-! Actual terminal Gibbs replicas transported to the retained marked cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma measurable_tensorTerminalLeafLaw {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    Measurable (tensorTerminalLeafLaw eig U c I degree amplitude n z) := by
  have hs : Measurable (fun p : (SpinTensorIndex I degree → ℝ) ×
      NoiseLeaf (SpinTensorIndex I degree → ℝ) n => tensorLeafState I degree n p.1 p.2) := by
    induction n with
    | zero => exact measurable_fst
    | succ n ih =>
      exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)
  have hw := (((measurable_spinTensorTerminal eig U c I degree amplitude).comp
    (hs.comp ((measurable_const (a := z)).prodMk measurable_id))).exp).ennreal_ofReal
  exact measurable_normalizeMass.comp
    ((measurable_withDensity_fixed hw).comp (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).measurable)

instance tensorTerminalLeafLaw_probability {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (T : NoiseTree (SpinTensorIndex I degree → ℝ) n) :
    IsProbabilityMeasure (tensorTerminalLeafLaw eig U c I degree amplitude n z T) :=
  normalizeMass_probability _

theorem tensor_terminal_replica_transport {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ((tensorCascadeLaw I degree n b v) ⊗ₘ
      probabilityReplicaKernel (tensorTerminalLeafLaw eig U c I degree amplitude n z)
        (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z)).map
      (fun p i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z (p.2 i)) =
    probabilityReplicaKernel (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n)
      (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).measurable ∘ₘ
      (tensorCascadeLaw I degree n b v).map
        (tensorRetainedCascade eig U c I degree amplitude n b v z) := by
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) := by
    unfold tensorCascadeLaw
    infer_instance
  apply sampling_replica_morphism
    (P := tensorCascadeLaw I degree n b v)
    (Q := (tensorCascadeLaw I degree n b v).map
      (tensorRetainedCascade eig U c I degree amplitude n b v z))
    (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z)
    (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).measurable
    (measurable_tensorRetainedCascade eig U c I degree amplitude n b v z) rfl
    (ψ := fun _ w => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
      (tensorCascadeStopped I degree n) z w)
  · exact ((measurable_noiseLeafKeep n
      (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
      (measurable_tensorCascadeStopped I degree n)).comp
        (measurable_const.prodMk measurable_id)).comp measurable_snd
  · exact tensorTerminalLeafLaw_keep_ae hN eig U c I degree amplitude n b v hb z

end InvariantIsing

end

end OAI
