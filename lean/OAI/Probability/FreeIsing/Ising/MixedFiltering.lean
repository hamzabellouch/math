import OAI.Probability.FreeIsing.Gibbs.CovarianceL2Limit
import OAI.Probability.FreeIsing.Ising.Innovation
import OAI.Probability.FreeIsing.Posterior.MixedFilteringCrossLimit
import OAI.Probability.FreeIsing.Posterior.PlantedArrayCrossEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

def covariance (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  infiniteGibbsCovariance beta v u
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

def finiteCovariance (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (n : ℕ) (t : ℝ≥0) (q : State d A) : ℝ :=
  finiteGibbsCovariance beta v u n
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

lemma measurable_covariance_joint
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v u : TreeVertex d) :
    Measurable (Function.uncurry (covariance beta B v u)) := by
  apply (measurable_infiniteGibbsCovariance beta v u).comp
  apply Measurable.of_eval
  intro i
  apply StronglyMeasurable.measurable
  change StronglyMeasurable (Function.uncurry
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray i))
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  · intro q
    exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    exact (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray i t).stronglyMeasurable

omit [MeasurableSpace A] in
lemma covariance_abs_le_two (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (t : ℝ≥0) (q : State d A) :
    |covariance beta B v u t q| ≤ 2 :=
  infiniteGibbsCovariance_abs_le_two beta v u _

lemma covariance_eq_condExp
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v u : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    covariance beta B v u t =ᵐ[P] fun q =>
      P[(fun q : State d A => spinSign (q.1 v) * spinSign (q.1 u)) | F t] q -
      P[(fun q : State d A => spinSign (q.1 v)) | F t] q * posterior beta B u t q := by
  have hc := hμ.infiniteGibbsCovariance_eq_brownian_past
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v u
  have hF : ArrayPosteriorStationarity.filtration (d := d) B hmB t =
      MeasurableSpace.comap
        (fun q : State d A => fun i (s : Set.Iic t) =>
          (s.1 : ℝ) * spinSign (q.1 i) + B s.1 (q.2 i)) inferInstance := by
    change arrayNaturalFiltration
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) t = _
    rw [arrayNaturalFiltration_eq_comap]
    congr 1
    funext q i s
    exact add_comm _ _
  rw [← hF] at hc
  have hp := posterior_eq_condExp hμ ν hB hmB t u
  filter_upwards [hc, hp] with q hq hu
  dsimp only [posteriorCovariance] at hq
  rw [hu]
  simpa only [covariance, plantedArrayObservation, ArrayPosteriorStationarity.spinArray,
    ArrayPosteriorStationarity.posterior, add_comm] using hq

lemma finiteCovariance_stronglyAdapted
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (v u : TreeVertex d) (n : ℕ) :
    StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB)
      (finiteCovariance beta B v u n) := by
  intro t
  have hobs : StronglyMeasurable[ArrayPosteriorStationarity.filtration B hmB t]
      (fun q : State d A => fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
        ArrayPosteriorStationarity.spinArray i t q) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d A) (TreeVertex d) (fun _ => ℝ)
      (ArrayPosteriorStationarity.filtration B hmB t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) i t).measurable
  exact (continuous_finiteGibbsCovariance beta v u n).comp_stronglyMeasurable hobs

omit [MeasurableSpace A] in
lemma finiteCovariance_continuous
    (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (n : ℕ) (q : State d A) :
    Continuous (fun t => finiteCovariance beta B v u n t q) := by
  apply (continuous_finiteGibbsCovariance beta v u n).comp
  apply continuous_pi
  intro i
  exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)

omit [MeasurableSpace A] in
lemma finiteCovariance_abs_le_two (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (n : ℕ) (t : ℝ≥0) (q : State d A) :
    |finiteCovariance beta B v u n t q| ≤ 2 :=
  finiteGibbsCovariance_abs_le_two beta v u n _

theorem tendsto_trial_cross_uniformSum
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) {H : ℝ≥0 → State d A → ℝ} {L : ℝ}
    (hH : StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB) H)
    (hcH : ∀ q, Continuous (fun t => H t q))
    (hL : 0 ≤ L) (hbH : ∀ t q, |H t q| ≤ L) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ q, posterior beta B v T q *
      BrownianGrid.uniformSum (innovation beta B u) H T n q
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
        H r.toNNReal q * covariance beta B v u r.toNNReal q
          ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hs (i : TreeVertex d) : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma i)) := (measurable_of_finite spinSign).comp (measurable_pi_apply i)
  have hb (i : TreeVertex d) : ∀ q : State d A, |spinSign (q.1 i)| ≤ (1 : ℝ) := by
    intro q
    cases q.1 i <;> norm_num [spinSign]
  have hobs := arrayNaturalFiltration_stronglyAdapted
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray) u
  have hl := FilteringCrossEnergy.tendsto_posterior_uniformSum_mixed_cross_energy
    (preBrownian_martingale_signalArrayFiltration μ (fun _ : TreeVertex d => ν)
      (fun _ => hB) (fun _ => hmB) u)
    (arrayObservationFiltration_le_signalArrayFiltration (fun _ : TreeVertex d => B)
      (fun _ => hmB) ArrayPosteriorStationarity.spinArray
      ArrayPosteriorStationarity.measurable_spinArray)
    (stronglyMeasurable_latent_signalArrayFiltration (fun _ : TreeVertex d => B)
      (fun _ => hmB) (hs v) 0)
    (Eventually.of_forall (hb v))
    (ArrayPosteriorStationarity.integrable_spin_coordinate P u)
    (Eventually.of_forall (hb u)) hobs (posterior_progressive beta B hmB hcB u)
    (fun t => posterior_eq_condExp hμ ν hB hmB t u)
    hH hcH hL hbH (measurable_covariance_joint beta B hmB hcB v u)
    (show (0 : ℝ) ≤ 2 by norm_num) (covariance_abs_le_two beta B v u)
    (fun t => covariance_eq_condExp hμ ν hB hmB t v u) T
  apply hl.congr
  intro n
  apply integral_congr_ae
  filter_upwards [posterior_eq_condExp hμ ν hB hmB T v] with q hq
  rw [hq]
  rfl

theorem tendsto_finiteCovariance_cross_uniformSum
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (k : ℕ) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ q, posterior beta B v T q *
      BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u k) T n q
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
        finiteCovariance beta B v u k r.toNNReal q * covariance beta B v u r.toNNReal q
          ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) :=
  tendsto_trial_cross_uniformSum hμ ν hB hmB hcB v u
    (finiteCovariance_stronglyAdapted beta B hmB v u k)
    (finiteCovariance_continuous beta B hcB v u k) (by norm_num)
    (finiteCovariance_abs_le_two beta B v u k) T

end Problem367.IsingInnovation

end

end OAI
