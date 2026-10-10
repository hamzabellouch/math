import OAI.Probability.InvariantIsing.Arrays.TensorLabeledSeedTransport
import OAI.Probability.InvariantIsing.Arrays.TensorLabeledAncestry
import OAI.Probability.InvariantIsing.Fields.NoiseReplicaPairData

namespace OAI

/-! Joint branch depth and increment paths in the original tensor terminal Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensor_labeled_seed_pair_law {N m k : ℕ} (hN : 0 < N)
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
          (fun p => (labeledCommonDepth n (p.2 0) (p.2 1),
            fun i => (p.1.2 (edgeAt n (p.2 0) i),p.1.2 (edgeAt n (p.2 1) i)))) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p => noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) := by
  obtain ⟨ψ,hψ,hψlaw,hfull⟩ := tensor_labeled_seed_replica_law hN eig U c I degree amplitude n b v hb
  refine ⟨ψ,hψ,hψlaw,fun z => ?_⟩
  have hm : Measurable (fun p : TensorCoordinateData I degree n × LabeledLeaf n =>
      noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z
        (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
          (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) p.2)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_noiseLeafKeep n
      (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
      (measurable_tensorCascadeStopped I degree n)).comp
        (measurable_const.prodMk
          ((measurable_labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n α).comp (by fun_prop)))
  have hK : Measurable (fun p : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n) =>
      fun i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z
        (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
          (p.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.1.2) (p.2 i))) :=
    Measurable.of_eval fun i => hm.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      fun i => cascadeSeedLeaf n ψ z (p.2 i)) :=
    Measurable.of_eval fun i => ((measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have h := congrArg (Measure.map (noiseReplicaPairData (A := SpinTensorIndex I degree → ℝ) n)) (hfull z)
  rw [Measure.map_map (measurable_noiseReplicaPairData n) hK,
    Measure.map_map (measurable_noiseReplicaPairData n) hS] at h
  refine (Measure.map_congr ?_).trans h
  filter_upwards [tensor_labeled_kept_depth_ae eig U c I degree amplitude n b v hb z] with p hp
  exact (noiseReplicaPairData_keep_labeled n
    (tensorCascadeMultiplier eig U c I degree amplitude n b v) (tensorCascadeStopped I degree n)
    z p.1.1 p.1.2 p.2 hp).symm

end InvariantIsing

end

end OAI
