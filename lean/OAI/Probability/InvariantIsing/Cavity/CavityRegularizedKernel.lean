import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedReweighting
import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerRegularization

namespace OAI

/-! Measurability and boundedness of the regularized replica mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma measurable_cavityRegularizedReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) (δ : ℝ) :
    Measurable (fun ω => cavityRegularizedReplicaMean (ν ω)
      (fun x => w (ω,x)) (fun σ => F (ω,σ)) δ) :=
  (measurable_cavityWeightNumerator ν hν w hw F hF).div
    (((measurable_cavityWeightNormalizer ν hν w hw).add_const δ).pow_const r)

lemma cavityRegularizedReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F)
    {M B δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hwb : ∀ x, w x ∈ Icc 0 M) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityRegularizedReplicaMean ν w F δ| ≤ B :=
  cavity_regularized_numerator_bound
    (cavityWeightNormalizer_mem ν w hw le_rfl hwb).1 hB hδ r
    (cavityWeightNumerator_abs_le_normalizer ν w hw F hF hM hB hwb hFb)

end InvariantIsing

end

end OAI
