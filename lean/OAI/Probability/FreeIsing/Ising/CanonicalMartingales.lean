import OAI.Probability.FreeIsing.Energy.ArtanhResponseCoefficients
import OAI.Probability.FreeIsing.Gibbs.CompensatedSquare
import OAI.Probability.FreeIsing.Ising.CanonicalPosteriorStops
import OAI.Probability.FreeIsing.Martingales.Pushforward

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma evaluation_progressive {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (evaluation v) :=
  (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation v).isStronglyProgressive_of_continuous
    (fun x => (x v).continuous)

 theorem canonical_posterior_martingale
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  apply MartingalePushforward.martingale_of_pullback (measurePreserving_uniformObservation μ)
    (F := ArrayPosteriorStationarity.filtration B hmB)
    (fun t => (filtration_comap_uniformObservation d t hmB).le)
    (posterior_progressive beta v).stronglyAdapted
  exact IsingInnovation.posterior_martingale hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB
    (fun u => (WienerSampler.sample u).continuous) v

 theorem continuousPosterior_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (continuousPosterior beta v) (filtration d) (observationLaw μ) :=
  (canonical_posterior_martingale hμ v).congr
    (continuousPosterior_progressive beta v).stronglyAdapted
    (fun t => ((continuousPosterior_modification hd hμ hb hcrit v).2 t).symm)

def canonicalCovarianceEnergy {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  ∑' w, infiniteGibbsCovariance beta v w (fun i => x i t) ^ 2

lemma canonicalCovarianceEnergy_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (canonicalCovarianceEnergy beta v) :=
  ArtanhResponseCoefficients.isStronglyProgressive_covarianceSquareRow _ beta v _ evaluation_progressive

def canonicalCovarianceCompensator {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℝ≥0 → Paths d → ℝ := nnrealTimePrimitive (canonicalCovarianceEnergy beta v)

lemma canonicalCovarianceCompensator_uniformObservation {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (q : IsingInnovation.State d ℝ) :
    canonicalCovarianceCompensator beta v t (uniformObservation q) =
      gibbsCovarianceCompensator beta v (fun _ s u => WienerSampler.sample u s) t q := by
  unfold canonicalCovarianceCompensator nnrealTimePrimitive gibbsCovarianceCompensator
  rw [intervalIntegral.integral_of_le t.coe_nonneg, intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  unfold canonicalCovarianceEnergy gibbsCovarianceEnergy
  apply tsum_congr
  intro w
  apply congrArg (fun z : ℝ => z ^ 2)
  apply congrArg (infiniteGibbsCovariance beta v w)
  funext i
  change WienerSampler.sample (q.2 i) r.toNNReal +
    (r.toNNReal : ℝ) * spinSign (q.1 i) =
      r * spinSign (q.1 i) + WienerSampler.sample (q.2 i) r.toNNReal
  rw [Real.coe_toNNReal r hr.1.le, add_comm]

 theorem canonical_compensatedSquare_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (fun t x => posterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x)
      (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  apply MartingalePushforward.martingale_of_pullback (measurePreserving_uniformObservation μ)
    (F := ArrayPosteriorStationarity.filtration B hmB)
    (fun t => (filtration_comap_uniformObservation d t hmB).le)
    (fun t => ((posterior_progressive beta v).stronglyAdapted t).pow 2 |>.sub
      ((isStronglyProgressive_nnrealTimePrimitive
        (canonicalCovarianceEnergy_progressive beta v)).stronglyAdapted t))
  have h := hμ.infiniteGibbsSpinMean_compensatedSquare_martingale hd hb hcrit
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ => hmB) (fun _ u => (WienerSampler.sample u).continuous) v
  convert h using 1
  funext t q
  change posterior beta v t (uniformObservation q) ^ 2 -
    canonicalCovarianceCompensator beta v t (uniformObservation q) = _
  rw [canonicalCovarianceCompensator_uniformObservation]
  have hp : posterior beta v t (uniformObservation q) =
      infiniteGibbsSpinMean beta v
        (brownianIsingObservationR (fun _ s u => WienerSampler.sample u s) ((t : ℝ), q)) := by
    rw [posterior_uniformObservation]
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    simp only [brownianIsingObservationR, Real.toNNReal_coe]
  rw [hp]
  all_goals rfl

 theorem continuousPosterior_compensatedSquare_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (fun t x => continuousPosterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x)
      (filtration d) (observationLaw μ) := by
  apply (canonical_compensatedSquare_martingale hd hμ hb hcrit v).congr
    (fun t => ((continuousPosterior_progressive beta v).stronglyAdapted t).pow 2 |>.sub
      ((isStronglyProgressive_nnrealTimePrimitive
        (canonicalCovarianceEnergy_progressive beta v)).stronglyAdapted t))
  intro t
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit v).2 t] with x hx
  change posterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x =
    continuousPosterior beta v t x ^ 2 - canonicalCovarianceCompensator beta v t x
  rw [hx]

end Problem367.IsingObservationFactor

end

end OAI
