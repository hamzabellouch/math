import OAI.Probability.InvariantIsing.Fields.CascadeSeedLeafLaw

namespace OAI

/-! The joint replica law under the finite ancestor-seed construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

theorem cascadeSeed_replica_law {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
      probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
      (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) =
    probabilityReplicaKernel (noiseLeafKernel (ι → ℝ) n) (noiseLeafKernel (ι → ℝ) n).measurable ∘ₘ
      (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
        (cascadeSeedTree n b ψ z) := by
  apply sampling_replica_morphism
    (P := (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)))
    (Q := (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
      (cascadeSeedTree n b ψ z))
    (noiseLeafKernel unitInterval n).measurable (noiseLeafKernel (ι → ℝ) n).measurable
    ((measurable_cascadeSeedTree n b ψ hψ).comp (measurable_const.prodMk measurable_id)) rfl
    (ψ := fun _ v => cascadeSeedLeaf n ψ z v)
  · exact ((measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk measurable_id)).comp measurable_snd
  · filter_upwards [cascadeSeedRegular_ae n b hb] with T hT
    exact cascadeSeedLeaf_law n b ψ hψ T hT z

end InvariantIsing

end

end OAI
