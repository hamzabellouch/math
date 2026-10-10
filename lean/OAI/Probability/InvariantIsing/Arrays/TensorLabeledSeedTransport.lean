import OAI.Probability.InvariantIsing.Arrays.TensorLabeledNoiseTransport
import OAI.Probability.InvariantIsing.Arrays.ReplicaPushforward

namespace OAI

/-! A seed representation of the original labeled terminal Gibbs replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensor_labeled_seed_replica_law {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    ∃ ψ : ℕ → (SpinTensorIndex I degree → ℝ) → unitInterval → (SpinTensorIndex I degree → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = tensorAncestorMarkKernel eig U c I degree amplitude n b v i z) ∧
      ∀ z,
        ((tensorCoordinateLaw I degree n b v) ⊗ₘ
          probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
            (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)).map
          (fun p i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
            (tensorCascadeStopped I degree n) z
            (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
              (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) (p.2 i))) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) := by
    unfold tensorCascadeLaw
    infer_instance
  obtain ⟨ψ,hψ,hψlaw,hseed⟩ := tensor_terminal_seed_replica_law hN eig U c I degree amplitude n b v hb
  refine ⟨ψ,hψ,hψlaw,fun z => ?_⟩
  have hkeep : Measurable (fun σ : ℕ → NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      fun i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z (σ i)) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_noiseLeafKeep n
      (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
      (measurable_tensorCascadeStopped I degree n)).comp
        ((measurable_const (a := z)).prodMk measurable_id)).comp (measurable_pi_apply i)
  have hleaf : Measurable (fun p : TensorCoordinateData I degree n × LabeledLeaf n =>
      labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
        (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) p.2) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n α).comp (by fun_prop)
  have hlabel : Measurable (fun p : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
        (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) (p.2 i)) :=
    Measurable.of_eval fun i => hleaf.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have h := congrArg (Measure.map (fun σ : ℕ → NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      fun i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z (σ i)))
    (tensor_labeled_noise_replica_law hN eig U c I degree amplitude n b v hb z)
  rw [Measure.map_map hkeep hlabel] at h
  exact h.trans ((map_compProd_snd (tensorCascadeLaw I degree n b v)
    (probabilityReplicaKernel (tensorTerminalLeafLaw eig U c I degree amplitude n z)
      (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z)) hkeep).symm.trans (hseed z))

end InvariantIsing

end

end OAI
