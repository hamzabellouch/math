import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalEnergy
import OAI.Probability.FreeIsing.Ising.MixedFiltering

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367.IsingInnovation
variable {d : ℕ} {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace A] in
lemma covariance_eq_brownianObservationR
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (v u : TreeVertex d)
    (p : ℝ × State d A) (hp : 0 ≤ p.1) :
    covariance beta B v u p.1.toNNReal p.2 =
      infiniteGibbsCovariance beta v u
        (brownianIsingObservationR (fun _ : TreeVertex d => B) p) := by
  unfold covariance
  apply congrArg (infiniteGibbsCovariance beta v u)
  funext i
  change B p.1.toNNReal (p.2.2 i) + (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) =
    p.1 * spinSign (p.2.1 i) + B p.1.toNNReal (p.2.2 i)
  rw [Real.coe_toNNReal _ hp]
  exact add_comm _ _

omit [MeasurableSpace A] in
lemma posterior_eq_brownianObservationR
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (p : State d A) :
    posterior beta B v t p =
      infiniteGibbsSpinMean beta v
        (brownianIsingObservationR (fun _ : TreeVertex d => B) ((t : ℝ), p)) := by
  unfold posterior
  apply congrArg (infiniteGibbsSpinMean beta v)
  funext i
  change B t (p.2 i) + (t : ℝ) * spinSign (p.1 i) =
    (t : ℝ) * spinSign (p.1 i) + B (t : ℝ).toNNReal (p.2 i)
  rw [Real.toNNReal_coe]
  exact add_comm _ _

theorem covariance_timeEnergy
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    let E := ∫ q, posterior beta B v T q ^ 2
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    HasSum (fun u => ∫ p : ℝ × State d A,
      covariance beta B v u p.1.toNNReal p.2 ^ 2 ∂P) E ∧
      (∫ p : ℝ × State d A,
        ∑' u, covariance beta B v u p.1.toNNReal p.2 ^ 2 ∂P) = E := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
  have htime : ∀ᵐ p : ℝ × State d A ∂P, 0 ≤ p.1 := by
    apply Measure.quasiMeasurePreserving_fst.ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ht.1.le
  have h := hμ.infiniteGibbsCovariance_timeEnergy_eq hd hb hcrit
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    (fun _ => hcB) v T.coe_nonneg
  dsimp only at h ⊢
  have heq (u : TreeVertex d) :
      (∫ p : ℝ × State d A, covariance beta B v u p.1.toNNReal p.2 ^ 2 ∂P) =
      ∫ p : ℝ × State d A, infiniteGibbsCovariance beta v u
        (brownianIsingObservationR (fun _ : TreeVertex d => B) p) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [htime] with p hp
    rw [covariance_eq_brownianObservationR beta B v u p hp]
  have hpost :
      (∫ q, posterior beta B v T q ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
      ∫ q, infiniteGibbsSpinMean beta v
        (brownianIsingObservationR (fun _ : TreeVertex d => B) ((T : ℝ), q)) ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      dsimp only
      rw [posterior_eq_brownianObservationR beta B v T q]
  rw [← hpost] at h
  constructor
  · convert h.1 using 1
    exact funext heq
  · calc
      _ = ∫ p : ℝ × State d A, ∑' u, infiniteGibbsCovariance beta v u
          (brownianIsingObservationR (fun _ : TreeVertex d => B) p) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [htime] with p hp
        apply tsum_congr
        intro u
        rw [covariance_eq_brownianObservationR beta B v u p hp]
      _ = _ := h.2

theorem covariance_timeEnergy_hasSum
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    HasSum (fun u => ∫ p : ℝ × State d A,
      covariance beta B v u p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
      (∫ q, posterior beta B v T q ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) :=
  (covariance_timeEnergy hμ hd hb hcrit ν hB hmB hcB v T).1

theorem covariance_timeEnergy_integral_eq
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    (∫ p : ℝ × State d A, ∑' u, covariance beta B v u p.1.toNNReal p.2 ^ 2
      ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) =
      ∫ q, posterior beta B v T q ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) :=
  (covariance_timeEnergy hμ hd hb hcrit ν hB hmB hcB v T).2

end Problem367.IsingInnovation

end

end OAI
