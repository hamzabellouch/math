import OAI.Analysis.LipschitzHilbert.Phase.DiagonalCarrier
import OAI.Analysis.LipschitzHilbert.Phase.GraphPhaseAverage

namespace OAI

/-!
# Uniform averages of the actual graph prediction

The band-limited probability is an explicit mixture. Its graph-prediction
average is at most one by the proved phase gain. Removing the path carrier
then bounds the lower deviation by the off-path coefficient mass, preserving
the relative path drop when passing to the principal probability.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

/-- The actual probability mixture used to approximate cell averages. -/
def predictionMixture (ω τ : Measure ℝ) (η : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - η) • ω + ENNReal.ofReal η • τ

omit [Fintype ι] [Fintype κ] in
theorem predictionMixture_isProbability (ω τ : Measure ℝ)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ] {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : IsProbabilityMeasure (predictionMixture ω τ η) := by
  constructor
  simp only [predictionMixture, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hη1) hη0]
  norm_num

theorem integrable_diagonal_energyRatio (μ : Measure ℝ) [IsFiniteMeasure μ]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ)
    {p : ℝ} (hp : 0 < p) (denominator : ℝ) :
    Integrable (fun t => energyRatio p denominator (diagonalFourierSum frequency a t)) μ := by
  have hmem : MemLp (diagonalFourierSum frequency a) (ENNReal.ofReal p) μ :=
    MemLp.of_bound (continuous_diagonalFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency a))
  have hi : Integrable (fun t => ‖diagonalFourierSum frequency a t‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hmem.integrable_norm_rpow'
  exact ((integrable_const 1).add hi).div_const denominator

/-- Uniform-average transfer for the actual diagonal phase sum, with the
constant denominator canceled through exact carrier removal. -/
theorem diagonal_prediction_mixture_transfer (ω τ : Measure ℝ)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) (i₀ : ι)
    {η p denominator B : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀, ‖a i‖) ≤ B)
    (haverage : (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t)
      ∂predictionMixture ω τ η) ≤ 1) :
    (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t) ∂ω) ≤
      1 + η / (1 - η) * (2 * p * B) := by
  have hp0 : 0 < p := by linarith
  have hω := integrable_diagonal_energyRatio ω frequency a hp0 denominator
  have hτ := integrable_diagonal_energyRatio τ frequency a hp0 denominator
  by_cases he : ∃ t, 1 < energyRatio p denominator (diagonalFourierSum frequency a t)
  · apply probability_mixture_average_le ω τ _ hη0 hη1 hω hτ _ haverage
    apply Filter.Eventually.of_forall
    intro t
    have h := diagonal_prediction_deficit frequency a i₀ hp hd hB hmass he t
    have hm := (le_max_left (1 - energyRatio p denominator (diagonalFourierSum frequency a t)) 0).trans h
    linarith
  · have hle : ∀ t, energyRatio p denominator (diagonalFourierSum frequency a t) ≤ 1 := by
      intro t
      exact le_of_not_gt (fun h => he ⟨t, h⟩)
    have hi : (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t) ∂ω) ≤ 1 := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono hω (integrable_const 1) hle
    exact hi.trans (le_add_of_nonneg_right (mul_nonneg
      (div_nonneg hη0 (sub_pos.mpr hη1).le) (by positivity)))

/-- The full graph-prediction average on the principal probability, after
paying only the off-path mass in the probability-mixture error. -/
theorem graph_prediction_uniform_average
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ω τ : Measure ℝ) [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι) {η gap D p B : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture ω τ η) gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀,
      ‖(((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i‖) ≤ B) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
        (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ω) ≤
      1 + η / (1 - η) * (2 * p * B) := by
  have := predictionMixture_isProbability ω τ hη0 hη1.le
  have hphase := graph_weighted_diagonal_prediction_average G hG w m hw hm
    (predictionMixture ω τ η) frequency l X lambda hgap hν hD hp
    hfrequency hcard hl htotal hlambda
  have hden : 0 < 1 + ∑ i, l i * ‖X i‖ ^ p :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
  exact diagonal_prediction_mixture_transfer ω τ frequency
    (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) i₀
    hη0 hη1 (by linarith) hden hB hmass hphase

end LipschitzHilbert

end

end OAI
