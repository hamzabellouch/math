import OAI.Probability.InvariantIsing.Fields.VectorLabeledSeedTransport
import OAI.Probability.InvariantIsing.Arrays.CoordinateReplicaAncestry
import OAI.Probability.InvariantIsing.Fields.NoiseReplicaPairData
import OAI.Probability.InvariantIsing.Arrays.CoordinatePairData

namespace OAI

/-! Joint ancestry and both complete paths for the original finite vector terminal. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_seed_pair_law {N : ℕ} (hN : 0 < N) (n : ℕ)
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
          (fun p => coordinatePairData n (p.1.2,p.2)) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p => noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) := by
  obtain ⟨ψ,hψ,hψlaw,hfull⟩ := vector_labeled_seed_replica_law hN n b v hb F hF hG
  refine ⟨ψ,hψ,hψlaw,fun z he => ?_⟩
  have hm : Measurable (fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
        (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) p.2)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp
      (measurable_const.prodMk ((measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)))
  have hK : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
        (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i))) :=
    Measurable.of_eval fun i => hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      fun i => cascadeSeedLeaf n ψ z (p.2 i)) :=
    Measurable.of_eval fun i => (measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hdepth := coordinate_sampled_ancestry_ae n b hb (fun i => vectorGaussianLaw N (v i))
    (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n)
    (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)
    (fun _ _ => (Real.exp_pos _).ne') z (vectorLabeledTerminalLaw N n F z)
    (measurable_vectorLabeledTerminalLaw N n F hF z)
    (fun p => gibbsProbability_absolutelyContinuous (labeledLeafLaw n p.1) _)
  have h := congrArg (Measure.map (noiseReplicaPairData (A := Fin N → ℝ) n)) (hfull z he)
  rw [Measure.map_map (measurable_noiseReplicaPairData n) hK,
    Measure.map_map (measurable_noiseReplicaPairData n) hS] at h
  refine (Measure.map_congr ?_).trans h
  filter_upwards [hdepth] with p hp
  exact (noiseReplicaPairData_keep_labeled n (vectorTerminalMultiplier N n b v F)
    (vectorTerminalUpdate N n) z p.1.1 p.1.2 p.2 hp).symm

end InvariantIsing

end

end OAI
