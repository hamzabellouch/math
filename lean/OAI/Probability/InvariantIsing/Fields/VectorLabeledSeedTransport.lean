import OAI.Probability.InvariantIsing.Fields.VectorLabeledNoiseTransport
import OAI.Probability.InvariantIsing.Fields.VectorTerminalSeed
import OAI.Probability.InvariantIsing.Arrays.ReplicaPushforward

namespace OAI

/-! Full labeled field replicas transported to the common uniform-seed construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_seed_replica_law {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z) ∧
      ∀ z, (∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
        Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
          (labeledLeafLaw n p.1)) →
        (vectorTerminalCoordinateLaw N n b v ⊗ₘ
          probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z)
            (measurable_vectorLabeledTerminalLaw N n F hF z)).map
          (fun p i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
            (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i))) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  obtain ⟨ψ,hψ,hψlaw,hseed⟩ := vectorTerminal_seed_replica_law hN n b v hb F hF hG
  refine ⟨ψ,hψ,hψlaw,fun z he => ?_⟩
  have hkeep : Measurable (fun σ : ℕ → NoiseLeaf (Fin N → ℝ) n =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (σ i)) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp
        ((measurable_const (a := z)).prodMk measurable_id)).comp (measurable_pi_apply i)
  have hleaf : Measurable (fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) p.2) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)
  have hlabel : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i)) :=
    Measurable.of_eval fun i => hleaf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have h := congrArg (Measure.map (fun σ : ℕ → NoiseLeaf (Fin N → ℝ) n =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (σ i)))
    (vector_labeled_noise_replica_law N n b v hb F hF z he)
  rw [Measure.map_map hkeep hlabel] at h
  exact h.trans ((map_compProd_snd
    (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n))
    (probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z)) hkeep).symm.trans (hseed z))

end InvariantIsing

end

end OAI
