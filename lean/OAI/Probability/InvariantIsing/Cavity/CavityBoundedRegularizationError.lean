import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedKernel
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffNormalizer

namespace OAI

/-! A quantitative denominator-removal bound for the restricted weights.
The prior tail controls the exceptional small-normalizer event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_bounded_regularization_mean_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (t : Ω → ℝ) (ht : Measurable t) (hti : Integrable t P) (ht0 : ∀ ω, 0 ≤ t ω)
    {M B δ a : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ha : 0 < a)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B)
    (hlow : ∀ ω, t ω ≤ 1/2 → a ≤ cavityWeightNormalizer (ν ω) (fun x => w (ω,x))) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω) (fun x => w (ω,x))
        (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
        (fun σ => F (ω,σ)) ∂P| ≤ B * r * δ / a + 4 * B * ∫ ω, t ω ∂P := by
  let Z ω := cavityWeightNormalizer (ν ω) (fun x => w (ω,x))
  let A ω := cavityWeightNumerator (ν ω) (fun x => w (ω,x)) (fun σ => F (ω,σ))
  have hZ : Measurable Z := measurable_cavityWeightNormalizer ν hν w hw
  have hA : Measurable A := measurable_cavityWeightNumerator ν hν w hw F hF
  have hZ0 ω : 0 ≤ Z ω :=
    (cavityWeightNormalizer_mem (ν ω) _ (hw.comp measurable_prodMk_left) le_rfl (hwb ω)).1
  have hAZ ω : |A ω| ≤ B * Z ω^r :=
    cavityWeightNumerator_abs_le_normalizer (ν ω) _ (hw.comp measurable_prodMk_left)
      _ (hF.comp measurable_prodMk_left) hM hB (hwb ω) (hFb ω)
  have hi : Integrable (fun ω => A ω / Z ω^r) P :=
    integrable_of_measurable_abs_le (hA.div (hZ.pow_const r))
      (fun ω => cavity_normalized_numerator_bound (hZ0 ω) hB r (hAZ ω))
  have hiδ : Integrable (fun ω => A ω / (Z ω + δ)^r) P :=
    integrable_of_measurable_abs_le (hA.div ((hZ.add_const δ).pow_const r))
      (fun ω => cavity_regularized_numerator_bound (hZ0 ω) hB hδ r (hAZ ω))
  have he := cavity_normalizer_regularization_mean_error P A Z hA hZ hB hδ ha r hZ0 hAZ
  have hp := cavity_small_normalizer_probability P Z t hZ ht hti ht0 hlow
  change |(∫ ω, A ω / (Z ω + δ)^r ∂P) - ∫ ω, A ω / Z ω^r ∂P| ≤ _
  rw [abs_sub_comm, ← integral_sub hi hiδ]
  exact he.trans (by nlinarith)

end InvariantIsing

end

end OAI
