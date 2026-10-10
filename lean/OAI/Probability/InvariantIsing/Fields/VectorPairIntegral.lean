import OAI.Probability.InvariantIsing.Fields.VectorLabeledPairLaw
import OAI.Probability.InvariantIsing.Fields.SeedPairIntegral
import OAI.Probability.InvariantIsing.Fields.SeedSharedKernel

namespace OAI

/-! The proved two-path formula for a finite Gaussian vector terminal. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

def vectorTerminalPairMean (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ)
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p : VectorTerminalCoordinates N n,
    referenceReplicaMean (labeledLeafLaw n p.1)
      (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z))
      (fun σ : Fin 2 → LabeledLeaf n => Φ
        (labeledCommonDepth n (σ 0) (σ 1),fun i => (p.2 (edgeAt n (σ 0) i),p.2 (edgeAt n (σ 1) i))))
      ∂vectorTerminalCoordinateLaw N n b v

lemma vectorTerminalPairMean_eq_integral (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1))
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    vectorTerminalPairMean N n b v F z Φ =
      ∫ q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n), Φ (coordinatePairData n (q.1.2,q.2))
        ∂(vectorTerminalCoordinateLaw N n b v ⊗ₘ
          probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)) := by
  have hm : Measurable (fun q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2))) :=
    hΦ.comp ((measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd))
  have hi : Integrable (fun q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2)))
      (vectorTerminalCoordinateLaw N n b v ⊗ₘ
        probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)) :=
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs] using hB _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [he] with p hp
  exact referenceReplicaMean_infinite (labeledLeafLaw n p.1)
    (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)) hp
    (fun σ : Fin 2 → LabeledLeaf n => Φ
      (labeledCommonDepth n (σ 0) (σ 1),fun i => (p.2 (edgeAt n (σ 0) i),p.2 (edgeAt n (σ 1) i))))
    (measurable_of_countable _)

theorem vectorTerminal_pair_formula {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1))
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    vectorTerminalPairMean N n b v F z Φ =
      ∫ α : ℕ → LabeledLeaf n,
        markPairPathMean n (vectorTerminalAncestorKernel N n b v F hF)
          (labeledCommonDepth n (α 0) (α 1)) z z
          (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b := by
  obtain ⟨ψ,hψ,hψlaw,hlaw⟩ := vector_labeled_seed_pair_law hN n b v hb F hF hG
  have hD : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      coordinatePairData n (p.1.2,p.2)) :=
    (measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd)
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) :=
    (measurable_noiseReplicaPairData n).comp (Measurable.of_eval fun i =>
      (measurable_cascadeSeedLeaf n ψ hψ).comp
        (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hi := congrArg (fun μ => ∫ x, Φ x ∂μ) (hlaw z he)
  rw [integral_map hD.aemeasurable hΦ.aestronglyMeasurable,
    integral_map hS.aemeasurable hΦ.aestronglyMeasurable] at hi
  rw [vectorTerminalPairMean_eq_integral N n b v F hF z he Φ hΦ hB,hi,
    seed_pair_mean_integral n b hb ψ hψ z Φ hΦ hB]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  exact seed_shared_kernel n (vectorTerminalAncestorKernel N n b v F hF)
    (fun i => vectorTerminalAncestorKernel_markov hN n b v hb F hF hG i)
    ψ hψ hψlaw (labeledCommonDepth n (α 0) (α 1)) z _
    (hΦ.comp (measurable_const.prodMk measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
