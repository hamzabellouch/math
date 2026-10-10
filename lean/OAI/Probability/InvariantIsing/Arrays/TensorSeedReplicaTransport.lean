import OAI.Probability.InvariantIsing.Arrays.TensorTerminalReplicaTransport

namespace OAI

/-! A common seed representation of all terminal-tilted Ising tensor replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensor_terminal_seed_replica_law {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) :
    ∃ ψ : ℕ → (SpinTensorIndex I degree → ℝ) → unitInterval → (SpinTensorIndex I degree → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = tensorAncestorMarkKernel eig U c I degree amplitude n b v i z) ∧
      ∀ z,
        ((tensorCascadeLaw I degree n b v) ⊗ₘ
          probabilityReplicaKernel (tensorTerminalLeafLaw eig U c I degree amplitude n z)
            (measurable_tensorTerminalLeafLaw eig U c I degree amplitude n z)).map
          (fun p i => noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
            (tensorCascadeStopped I degree n) z (p.2 i)) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  obtain ⟨ψ,hψ,hψlaw,hTree⟩ := tensorRetainedCascade_seed_law hN eig U c I degree amplitude n b v hb
  refine ⟨ψ,hψ,hψlaw,fun z => ?_⟩
  rw [tensor_terminal_replica_transport hN eig U c I degree amplitude n b v hb z,
    ← hTree z, ← cascadeSeed_replica_law n b hb ψ hψ z]

end InvariantIsing

end

end OAI
