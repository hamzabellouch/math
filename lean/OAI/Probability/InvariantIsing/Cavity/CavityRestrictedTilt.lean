import OAI.Probability.InvariantIsing.Cavity.CavityContinuousReplicaTilt
import OAI.Probability.InvariantIsing.Cavity.CavitySoftCutoff

namespace OAI

/-! Restricting an exponential Gibbs weight commutes with normalizing its
full tilt, including when the restricted normalizer is zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityWeightedReplicaMean_mul_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (fun x => w x * Real.exp (H x)) F =
      cavityWeightedReplicaMean (ν.tilted H) w F := by
  have hn : cavityWeightNumerator (ν.tilted H) w F =
      cavityWeightNumerator ν (fun x => w x * Real.exp (H x)) F /
        (∫ x, Real.exp (H x) ∂ν)^r := by
    unfold cavityWeightNumerator
    rw [← cavity_continuous_replica_tilt ν H he r, integral_tilted_eq_div,
      cavity_exp_replica_partition]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with σ
    rw [Real.exp_sum, Finset.prod_mul_distrib]
    ring
  have hz : cavityWeightNormalizer (ν.tilted H) w =
      cavityWeightNormalizer ν (fun x => w x * Real.exp (H x)) /
        (∫ x, Real.exp (H x) ∂ν) := by
    unfold cavityWeightNormalizer
    rw [integral_tilted_eq_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  rw [cavityWeightedReplicaMean, cavityWeightedReplicaMean, hn, hz, div_pow,
    div_div_div_cancel_right₀ (pow_ne_zero r (integral_exp_pos he).ne')]

lemma cavityWeightedReplicaMean_indicator_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (s : Set X)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F =
      cavityWeightedReplicaMean (ν.tilted H) (s.indicator (fun _ => 1)) F := by
  convert cavityWeightedReplicaMean_mul_exp ν H he (s.indicator (fun _ => 1)) F using 1
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem cavity_restricted_replica_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (s : Set X) (hs : MeasurableSet s)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F -
      cavityWeightedReplicaMean ν (fun x => Real.exp (H x)) F| ≤
        2 * B * r * (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted he
  rw [cavityWeightedReplicaMean_indicator_exp ν H he,
    cavityWeightedReplicaMean_exp ν H he]
  have hb x : s.indicator (fun _ => (1 : ℝ)) x ∈ Icc 0 1 := by
    by_cases hx : x ∈ s <;> simp [hx]
  have hh := cavity_soft_cutoff_replica_error (ν.tilted H)
    (s.indicator (fun _ => 1)) (measurable_const.indicator hs) hb F hF hB hFb
  have hz : cavityWeightNormalizer (ν.tilted H) (s.indicator (fun _ => (1 : ℝ))) =
      (ν.tilted H).real s := integral_indicator_one hs
  simpa only [hz, measureReal_compl hs, probReal_univ] using hh

end InvariantIsing

end

end OAI
