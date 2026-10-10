import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Ising.CopyBrownian
import OAI.Probability.FreeIsing.Ising.CopyEnergyIntegrability

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

def response (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  continuousRootResponse hb v t (projection j q)

def covariance (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  continuousRootCovariance hb v t (projection j q)

lemma projection_measurable (j : Bool) : Measurable (projection (d := d) j) := by
  cases j
  · exact measurable_snd.comp measurable_snd
  · exact measurable_fst.comp measurable_snd

lemma projection_preserving {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingCopyStationarity.measurePreserving_observations
    (beta := beta) (μ := μ)
  cases j
  · exact hr
  · exact hl

lemma field_progressive (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => continuousField beta v t (projection j q)) := by
  have hobs (i : TreeVertex d) : IsStronglyProgressive
      ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => projection j q i t) := by
    cases j
    · exact IsingConditionalCopyBounds.progressive_rightObservation i
    · exact IsingConditionalCopyBounds.progressive_leftObservation i
  have hraw := isStronglyProgressive_artanh _
    (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _ hobs)
  exact ProgressiveVersionPushforward.progressive_version hraw

lemma response_progressive (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration (response hb j v) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun vertex => (field_progressive j vertex T).measurable))).stronglyMeasurable

private lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh_response x).continuousAt)

lemma covariance_progressive (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration (covariance hb j v) := by
  intro T
  exact (stronglyMeasurable_const.sub
    ((continuous_tanh.comp_stronglyMeasurable
      (field_progressive j (ConnectedHull.root d) T)).pow 2)).mul
        (response_progressive hb j v T)

lemma response_abs_le_one (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : |response hb j v t q| ≤ 1 :=
  continuousRootResponse_abs_le_one hb v t (projection j q)

lemma covariance_abs_le_one (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : |covariance hb j v t q| ≤ 1 :=
  continuousRootCovariance_abs_le_one hb v t (projection j q)

lemma covariance_sq_le_response_sq (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : covariance hb j v t q ^ 2 ≤ response hb j v t q ^ 2 := by
  have hz := Real.tanh_sq_lt_one (continuousField beta (ConnectedHull.root d) t (projection j q))
  have hn := sq_nonneg (Real.tanh (continuousField beta (ConnectedHull.root d) t (projection j q)))
  change ((1 - Real.tanh (continuousField beta (ConnectedHull.root d) t (projection j q)) ^ 2) *
      response hb j v t q) ^ 2 ≤ _
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma response_continuous_ae (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t => response hb j v t q) :=
  (projection_preserving (beta := beta) (μ := μ) j).quasiMeasurePreserving.ae
    (continuousRootResponse_continuous_ae hd hμ hb hcrit v)

lemma covariance_continuous_ae (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t => covariance hb j v t q) :=
  (projection_preserving (beta := beta) (μ := μ) j).quasiMeasurePreserving.ae
    (continuousRootCovariance_continuous_ae hd hμ hb hcrit v)

lemma response_eq_raw_ae (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) (t : ℝ≥0) :
    response hb j v t =ᵐ[copies beta μ] fun q =>
      infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => projection j q i t) :=
  (projection_preserving (beta := beta) (μ := μ) j).quasiMeasurePreserving.ae
    (continuousRootResponse_eq_response_ae hd hμ hb hcrit v t)

lemma covariance_eq_raw_ae (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) (t : ℝ≥0) :
    covariance hb j v t =ᵐ[copies beta μ] fun q =>
      infiniteGibbsCovariance beta (ConnectedHull.root d) v (fun i => projection j q i t) :=
  (projection_preserving (beta := beta) (μ := μ) j).quasiMeasurePreserving.ae
    (continuousRootCovariance_eq_covariance_ae hd hμ hb hcrit v t)

private lemma real_measurable {X : ℝ≥0 → Joint d → ℝ}
    (hX : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration X) :
    Measurable (fun p : ℝ × Joint d => X p.1.toNNReal p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive hX).measurable.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

private lemma sq_time_integrable {X : ℝ≥0 → Joint d → ℝ}
    (hX : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration X)
    (hb : ∀ t q, |X t q| ≤ 1) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => X p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  have hp : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t q => X t q ^ 2) := fun t => (hX t).pow 2
  have h := integrable_nnreal_process_interval_of_progressive_bounded
    (P := copies beta μ) hp 1
    (fun t => Eventually.of_forall fun q => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb t q, neg_abs_le (X t q), le_abs_self (X t q)]) 0 T
  simpa only [NNReal.coe_zero] using h

theorem response_row_energy (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (T : ℝ≥0) :
    (∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)),
      Summable (fun v => response hb j v p.1.toNNReal p.2 ^ 2)) ∧
    Integrable (fun p : ℝ × Joint d => ∑' v, response hb j v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  have he (v : TreeVertex d) :
      (fun p : ℝ × Joint d => response hb j v p.1.toNNReal p.2) =ᵐ[
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)]
      fun p => responseRow beta (ConnectedHull.root d) v (timeProjection j p) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (real_measurable (response_progressive hb j v))
      ((measurable_responseRow beta (ConnectedHull.root d) v).comp
        (measurable_fst.prodMk ((projection_measurable j).comp measurable_snd))))).2
    exact Eventually.of_forall fun t => response_eq_raw_ae hd hμ hb hcrit j v t.toNNReal
  have hall := ae_all_iff.mpr he
  have hraw := copy_row_energy_integrable hμ hb (ConnectedHull.root d) j T.coe_nonneg
  constructor
  · filter_upwards [hall, hraw.1] with p hp hs
    simpa only [hp] using hs
  · apply hraw.2.1.congr
    filter_upwards [hall] with p hp
    exact tsum_congr (fun v => congrArg (fun x : ℝ => x ^ 2) (hp v).symm)

theorem response_energy_summable (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (T : ℝ≥0) :
    Summable (fun v => ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      response hb j v s.toNNReal q ^ 2 ∂copies beta μ) := by
  obtain ⟨hs, hi⟩ := response_row_energy hd hμ hb hcrit j T
  have h := (DiscrepancyEnergy.hasSum_integral_sq_row
    (fun v => (real_measurable (response_progressive hb j v)).aestronglyMeasurable) hs hi).summable
  have he (v : TreeVertex d) :
      (∫ p : ℝ × Joint d, response hb j v p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ q, response hb j v s.toNNReal q ^ 2 ∂copies beta μ := by
    rw [integral_prod _ (sq_time_integrable (response_progressive hb j v)
      (response_abs_le_one hb j v) T), intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [he] using h

theorem covariance_energy_summable (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (T : ℝ≥0) :
    Summable (fun v => ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      covariance hb j v s.toNNReal q ^ 2 ∂copies beta μ) := by
  apply Summable.of_nonneg_of_le
    (fun v => intervalIntegral.integral_nonneg T.coe_nonneg
      (fun s _ => integral_nonneg (fun q => sq_nonneg _)))
    _ (response_energy_summable hd hμ hb hcrit j T)
  intro v
  have hC := sq_time_integrable (covariance_progressive hb j v)
    (covariance_abs_le_one hb j v) T (beta := beta) (μ := μ)
  have hR := sq_time_integrable (response_progressive hb j v)
    (response_abs_le_one hb j v) T (beta := beta) (μ := μ)
  rw [intervalIntegral.integral_of_le T.coe_nonneg, intervalIntegral.integral_of_le T.coe_nonneg,
    ← integral_prod _ hC, ← integral_prod _ hR]
  exact integral_mono hC hR (fun p => covariance_sq_le_response_sq hb j v p.1.toNNReal p.2)

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
