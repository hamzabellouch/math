import OAI.Probability.InvariantIsing.Fields.CascadeSeedPairCoordinates
import OAI.Probability.InvariantIsing.Fields.SeedSharedPairEvaluation

namespace OAI

/-! Averaging the exact shared-prefix seed recursion over the unperturbed cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_pair_mean_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ)
    (Φ : ℕ × (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    (∫ p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n),
      Φ (noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i)))
      ∂((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
        probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable)) =
    ∫ α : ℕ → LabeledLeaf n, seedPairPathMean n ψ (labeledCommonDepth n (α 0) (α 1)) z z
      (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b := by
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) :=
    (measurable_noiseReplicaPairData n).comp (Measurable.of_eval fun i =>
      (measurable_cascadeSeedLeaf n ψ hψ).comp
        (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hG : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
      Φ (seedForestPairData n ψ z q)) := hΦ.comp (measurable_seedForestPairData n ψ hψ z)
  have hiG : Integrable (fun q => Φ (seedForestPairData n ψ z q))
      ((cascadeReplicaLaw n b).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) :=
    Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs] using hB _)
  have h := congrArg (fun μ => ∫ p, Φ p ∂μ) (cascade_seed_pair_coordinates n b hb ψ hψ z)
  rw [integral_map hS.aemeasurable hΦ.aestronglyMeasurable,
    integral_map (measurable_seedForestPairData n ψ hψ z).aemeasurable hΦ.aestronglyMeasurable] at h
  rw [h,integral_prod _ hiG]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  exact seed_shared_pair_evaluation n ψ hψ z z (α 0) (α 1)
    (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w))
    (hΦ.comp (measurable_const.prodMk measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
