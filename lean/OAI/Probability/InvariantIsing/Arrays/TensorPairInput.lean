import OAI.Probability.InvariantIsing.Arrays.TensorSeedPairLaw
import OAI.Probability.InvariantIsing.Arrays.TensorTiltedPairIntegral
import OAI.Probability.InvariantIsing.Arrays.TensorMarkPairRecursion
import OAI.Probability.InvariantIsing.Fields.SeedPairIntegral
import OAI.Probability.InvariantIsing.Fields.SeedSharedKernel

namespace OAI

/-! The finite tensor marked-path specialization of PT2007, proved from the retained tree law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem panchenkoTalagrandTensorPair_proved : PanchenkoTalagrandTensorPairInput := by
  intro N m k hN eig U c I degree amplitude n b v hb z Φ hΦ hB
  obtain ⟨C,hB⟩ := hB
  obtain ⟨ψ,hψ,hψlaw,hlaw⟩ := tensor_labeled_seed_pair_law hN eig U c I degree amplitude n b v hb
  let P := tensorCoordinateLaw I degree n b v ⊗ₘ
    probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
      (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
  let Q := (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
    probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable
  let D := fun p : TensorCoordinateData I degree n × (ℕ → LabeledLeaf n) =>
    coordinatePairData n (p.1.2,p.2)
  let S := fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
    noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))
  have hD : Measurable D := (measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd)
  have hS : Measurable S := (measurable_noiseReplicaPairData n).comp
    (Measurable.of_eval fun i => (measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have he : P.map D = Q.map S := hlaw z
  have hi := congrArg (fun μ => ∫ x, Φ x ∂μ) he
  rw [integral_map hD.aemeasurable hΦ.aestronglyMeasurable,
    integral_map hS.aemeasurable hΦ.aestronglyMeasurable] at hi
  calc
    _ = ∫ p, Φ (D p) ∂P := tensorTiltedPairPathMean_eq_integral hN eig U c I degree amplitude n b v hb z Φ hΦ hB
    _ = ∫ p, Φ (S p) ∂Q := hi
    _ = ∫ α : ℕ → LabeledLeaf n,
        seedPairPathMean n ψ (labeledCommonDepth n (α 0) (α 1)) z z
          (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b :=
      seed_pair_mean_integral n b hb ψ hψ z Φ hΦ hB
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro α
      dsimp only
      rw [seed_shared_kernel n
        (fun i => tensorAncestorMarkKernel eig U c I degree amplitude n b v i)
        (fun i => tensorAncestorMarkKernel_markov hN eig U c I degree amplitude n b v hb i)
        ψ hψ hψlaw (labeledCommonDepth n (α 0) (α 1)) z
        (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w))
        (hΦ.comp (measurable_const.prodMk measurable_id)) (fun w => hB _)]
      simpa only [Nat.add_zero,Nat.sub_zero] using tensor_mark_pair_recursion eig U c I degree amplitude
        n b v (labeledCommonDepth n (α 0) (α 1)) n 0 z z
        (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w))

end InvariantIsing

end

end OAI
