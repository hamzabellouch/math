import OAI.Probability.FreeIsing.Energy.TimeRowEnergyHasSum
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Ising.CopyEnergyIntegrability

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

private theorem measurable_real_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : IsStronglyProgressive F M) :
    Measurable (fun p : ℝ × Ω => M p.1.toNNReal p.2) := by
  have hj : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hM).measurable
  have ht : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact hj.comp ht

private theorem measurable_response_real (hb : 0 ≤ beta) (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => continuousRootResponse hb v p.1.toNNReal p.2) :=
  measurable_real_of_progressive (continuousRootResponse_progressive hb v)

private theorem measurable_covariance_real (hb : 0 ≤ beta) (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => continuousRootCovariance hb v p.1.toNNReal p.2) :=
  measurable_real_of_progressive (continuousRootCovariance_progressive hb v)

theorem continuousRootResponse_row_eq_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ) :
    ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ),
      ∀ v, continuousRootResponse hb v p.1.toNNReal p.2 =
        IsingCopyEnergy.responseRow beta (ConnectedHull.root d) v p := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_response_real hb v)
    (IsingCopyEnergy.measurable_responseRow beta (ConnectedHull.root d) v))).mpr
  exact Eventually.of_forall fun t =>
    continuousRootResponse_eq_response_ae hd hμ hb hcrit v t.toNNReal

theorem continuousRootResponse_row_energy
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ),
      Summable (fun v => continuousRootResponse hb v p.1.toNNReal p.2 ^ 2)) ∧
    Integrable (fun p : ℝ × Paths d => ∑' v,
      continuousRootResponse hb v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) ∧
    (∫ p : ℝ × Paths d, ∑' v, continuousRootResponse hb v p.1.toNNReal p.2 ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  have hraw := IsingCopyEnergy.observation_row_energy_integrable hμ hb
    (ConnectedHull.root d) hT
  have he := continuousRootResponse_row_eq_ae hd hμ hb hcrit T
  have hsum : (fun p : ℝ × Paths d => ∑' v,
      continuousRootResponse hb v p.1.toNNReal p.2 ^ 2) =ᵐ[
        (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)]
      (fun p => ∑' v, IsingCopyEnergy.responseRow beta (ConnectedHull.root d) v p ^ 2) := by
    filter_upwards [he] with p hp
    exact tsum_congr (fun v => congrArg (fun r : ℝ => r ^ 2) (hp v))
  refine ⟨?_, hraw.2.1.congr hsum.symm, (integral_congr_ae hsum).trans_le hraw.2.2⟩
  filter_upwards [he, hraw.1] with p hp hs
  simpa only [hp] using hs

theorem continuousRootResponse_hasSum_timeEnergy
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    HasSum (fun v => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ x, continuousRootResponse hb v t.toNNReal x ^ 2 ∂observationLaw μ)
      (∫ p : ℝ × Paths d, ∑' v, continuousRootResponse hb v p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have h := continuousRootResponse_row_energy hd hμ hb hcrit T.coe_nonneg
  exact DiscrepancyEnergy.hasSum_intervalIntegral_sq_row T
    (fun v => (measurable_response_real hb v).aestronglyMeasurable) h.1 h.2.1

theorem continuousRootCovariance_sq_le_response_sq
    (hb : 0 ≤ beta) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) :
    continuousRootCovariance hb v t x ^ 2 ≤ continuousRootResponse hb v t x ^ 2 := by
  have h0 : 0 ≤ 1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2 :=
    (sub_pos.mpr (Real.tanh_sq_lt_one _)).le
  have h1 : 1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2 ≤ 1 :=
    sub_le_self _ (sq_nonneg _)
  have hs : (1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2) ^ 2 ≤ 1 := by
    nlinarith
  rw [continuousRootCovariance, mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

theorem continuousRootCovariance_row_energy
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ),
      Summable (fun v => continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2)) ∧
    Integrable (fun p : ℝ × Paths d => ∑' v,
      continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) ∧
    (∫ p : ℝ × Paths d, ∑' v, continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  have hR := continuousRootResponse_row_energy hd hμ hb hcrit hT
  have hs : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ),
      Summable (fun v => continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2) := by
    filter_upwards [hR.1] with p hp
    exact Summable.of_nonneg_of_le (fun v => sq_nonneg _)
      (fun v => continuousRootCovariance_sq_le_response_sq hb v _ _) hp
  have hle : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ),
      (∑' v, continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2) ≤
        ∑' v, continuousRootResponse hb v p.1.toNNReal p.2 ^ 2 := by
    filter_upwards [hs, hR.1] with p hcp hrp
    exact hcp.tsum_le_tsum
      (fun v => continuousRootCovariance_sq_le_response_sq hb v _ _) hrp
  have hi : Integrable (fun p : ℝ × Paths d => ∑' v,
      continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
    apply hR.2.1.mono'
      (Measurable.tsum (fun v => (measurable_covariance_real hb v).pow_const 2)).aestronglyMeasurable
    filter_upwards [hle] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg
      (fun v => sq_nonneg (continuousRootCovariance hb v p.1.toNNReal p.2)))]
    exact hp
  exact ⟨hs, hi, (integral_mono_ae hi hR.2.1 hle).trans hR.2.2⟩

theorem continuousRootCovariance_hasSum_timeEnergy
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    HasSum (fun v => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ x, continuousRootCovariance hb v t.toNNReal x ^ 2 ∂observationLaw μ)
      (∫ p : ℝ × Paths d, ∑' v, continuousRootCovariance hb v p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have h := continuousRootCovariance_row_energy hd hμ hb hcrit T.coe_nonneg
  exact DiscrepancyEnergy.hasSum_intervalIntegral_sq_row T
    (fun v => (measurable_covariance_real hb v).aestronglyMeasurable) h.1 h.2.1

end Problem367.IsingObservationFactor

end

end OAI
