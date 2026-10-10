import OAI.Probability.InvariantIsing.Fields.VectorTerminalNoise
import OAI.Probability.InvariantIsing.Fields.CascadeSeedRetainedLaw

namespace OAI

/-! Joint uniform-seed representation for terminal-tilted finite Gaussian vector fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vectorTerminal_seed_replica_law {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z) ∧
      ∀ z,
        (((noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n))) ⊗ₘ
          probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z)).map
          (fun p i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (p.2 i)) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  obtain ⟨ψ,hψ,hlaw⟩ := vectorTerminalAncestorKernel_seed hN n b v hb F hF hG
  refine ⟨ψ,hψ,hlaw,fun z => ?_⟩
  have htree := cascadeSeedTree_retained_law n b (fun i => vectorGaussianLaw N (v i))
    (vectorTerminalMultiplier N n b v F) ψ (measurable_vectorTerminalMultiplier N n b v F hF) hψ
    (fun _ _ _ => Real.exp_pos _) (vectorTerminalMultiplier_moment hN n b v hb F hF hG) hlaw z
  have htree' : (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
      (cascadeSeedTree n b ψ z) =
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)).map
        (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
          (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z) := by
    apply htree.trans
    apply congrArg (fun f : NoiseTree (Fin N → ℝ) n → NoiseTree (Fin N → ℝ) n => Measure.map f (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)))
    funext T
    apply noiseTreeKeep_update_congr
    intro i hi
    funext p
    simp only [vectorTerminalUpdate,stoppedUpdate,hi,ite_true]
  have hkeep := sampling_replica_morphism
    (P := (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)))
    (Q := (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)).map
      (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
        (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z))
    (T := noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
      (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z)
    (measurable_vectorTerminalNoiseLaw N n F hF z) (noiseLeafKernel (Fin N → ℝ) n).measurable
    ((measurable_noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
      (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)).comp
      ((measurable_const (a := z)).prodMk measurable_id)) rfl
    (ψ := fun _ w => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z w)
    (((measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp ((measurable_const (a := z)).prodMk measurable_id)).comp measurable_snd)
    (vectorTerminalNoiseLaw_keep_ae hN n b v hb F hF hG z)
  rw [hkeep,← htree',← cascadeSeed_replica_law n b hb ψ hψ z]

end InvariantIsing

end

end OAI
