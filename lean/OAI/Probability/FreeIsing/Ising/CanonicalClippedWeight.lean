import OAI.Probability.FreeIsing.Estimates.ClippedArtanhWeight
import OAI.Probability.FreeIsing.Ising.CanonicalArtanh
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralLocality

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.ClippedArtanhWeight
open ArtanhMartingaleFormula PosteriorCompensatorStopping PosteriorStoppingTimes

theorem weight_eq_stopped_before_exit {Ω : Type*}
    {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0)
    (n : ℕ) (t : ℝ≥0) (ht : (t : WithTop ℝ≥0) ≤ jointExit M A n ω) :
    weight (threshold n) (M t ω) =
      firstWeight (stoppedProcess M (jointExit M A n) t ω) := by
  have hb := abs_stopped_posterior_le (A := A) hc hzero n t
  rw [stoppedProcess_eq_of_le ht] at hb ⊢
  exact weight_eq_of_abs_le hb

end Problem367.ClippedArtanhWeight

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation ArtanhMartingaleFormula
open PosteriorStoppingTimes PosteriorCompensatorStopping

def canonicalClippedWeight {d : ℕ} (beta : ℝ) (n : ℕ)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  ClippedArtanhWeight.weight (threshold n)
    (continuousPosterior beta (ConnectedHull.root d) t x)

lemma canonicalClippedWeight_progressive {d : ℕ} (beta : ℝ) (n : ℕ) :
    IsStronglyProgressive (filtration d) (canonicalClippedWeight beta n) := by
  intro T
  exact (ClippedArtanhWeight.continuous_weight (threshold_nonneg n) (threshold_lt_one n)).comp_stronglyMeasurable
    (continuousPosterior_progressive beta (ConnectedHull.root d) T)

lemma canonicalClippedWeight_bound {d : ℕ} (beta : ℝ) (n : ℕ)
    (t : ℝ≥0) (x : Paths d) :
    |canonicalClippedWeight beta n t x| ≤ 1 / (1 - threshold n ^ 2) :=
  ClippedArtanhWeight.abs_weight_le (threshold_nonneg n) (threshold_lt_one n) _

theorem canonicalClippedWeight_continuous_ae
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => canonicalClippedWeight beta n t x) := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1]
    with x hx
  exact (ClippedArtanhWeight.continuous_weight (threshold_nonneg n) (threshold_lt_one n)).comp hx

theorem canonicalClippedWeight_mul_covariance_before_exit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) :
    ∀ᵐ x ∂observationLaw μ, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) ≤ canonicalPosteriorExit beta (ConnectedHull.root d) n x →
      ∀ w, canonicalClippedWeight beta n t x * continuousRootCovariance hb w t x =
        continuousRootResponse hb w t x := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousPosterior_initial_zero hd hμ hb hcrit (ConnectedHull.root d)] with x hc hz
  intro t ht w
  have hm := abs_stopped_posterior_le
    (A := canonicalCovarianceCompensator beta (ConnectedHull.root d)) hc hz n t
  change (t : WithTop ℝ≥0) ≤ jointExit
    (continuousPosterior beta (ConnectedHull.root d))
    (canonicalCovarianceCompensator beta (ConnectedHull.root d)) n x at ht
  rw [stoppedProcess_eq_of_le ht] at hm
  exact ClippedArtanhWeight.weight_mul_covariance_eq (threshold_nonneg n) (threshold_lt_one n) hm rfl

theorem canonicalClippedWeight_uniformSum_eq
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    let M := continuousPosterior beta (ConnectedHull.root d)
    let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
    BrownianGrid.uniformSum (stoppedProcess M τ) (canonicalClippedWeight beta n) T k
      =ᵐ[observationLaw μ]
        BrownianGrid.uniformSum (stoppedProcess M τ)
          (fun t x => firstWeight (stoppedProcess M τ t x)) T k := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousPosterior_initial_zero hd hμ hb hcrit (ConnectedHull.root d)] with x hc hz
  apply StoppedIntegralLocality.uniformSum_stopped_congr
  intro t ht
  exact ClippedArtanhWeight.weight_eq_stopped_before_exit hc hz n t ht

end Problem367.IsingObservationFactor

end

end OAI
