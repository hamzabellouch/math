import OAI.Probability.InvariantIsing.Arrays.CoordinateReplicaAncestry
import OAI.Probability.InvariantIsing.Arrays.TensorLabeledTerminal

namespace OAI

/-! Exact branch-depth preservation for the actual tensor Gibbs replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensor_labeled_kept_depth_ae {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ q ∂(tensorCoordinateLaw I degree n b v) ⊗ₘ
        probabilityReplicaKernel (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
          (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z),
      noiseLeafCommonDepth n
        (noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
          (tensorCascadeStopped I degree n) z
          (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
            (q.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.1.2) (q.2 0)))
        (noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
          (tensorCascadeStopped I degree n) z
          (labeledNoiseLeaf (SpinTensorIndex I degree → ℝ) n
            (q.1.1,markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.1.2) (q.2 1))) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  exact coordinate_sampled_ancestry_ae n b hb (fun i => tensorGaussianLaw I degree (v i))
    (tensorCascadeMultiplier eig U c I degree amplitude n b v) (tensorCascadeStopped I degree n)
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
    (measurable_tensorCascadeStopped I degree n)
    (fun i p => (tensorCascadeMultiplier_pos eig U c I degree amplitude n b v i p.1 p.2).ne') z
    (tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
    (measurable_tensorLabeledTerminalGibbs eig U c I degree amplitude n z)
    (fun p => gibbsProbability_absolutelyContinuous (labeledLeafLaw n p.1) _)

end InvariantIsing

end

end OAI
