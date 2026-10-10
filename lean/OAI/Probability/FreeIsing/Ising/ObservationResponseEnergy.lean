import OAI.Probability.FreeIsing.Critical.ResponseIntrinsic
import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Ising.CopyStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Problem367.IsingObservationResponseEnergy

open IsingObservationInnovation IsingObservationFactor PlantedSymmetry
open CriticalCanonicalRowEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def response (beta : ℝ) (u v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ :=
  infiniteGibbsResponse beta u v (fun i => x i t)

theorem measurable_response (beta : ℝ) (u v : TreeVertex d) (t : ℝ≥0) :
    Measurable (response beta u v t) :=
  (measurable_infiniteGibbsResponse beta u v).comp
    (Measurable.of_eval fun coordinate => measurable_evaluation coordinate t)

theorem measurable_response_joint (beta : ℝ) (u v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × Paths d => response beta u v p.1 p.2) := by
  apply (measurable_infiniteGibbsResponse beta u v).comp
  exact Measurable.of_eval fun coordinate => continuous_eval.measurable.comp
    (((measurable_pi_apply coordinate).comp measurable_snd).prodMk measurable_fst)

theorem observation_snapshot_identDistrib (t : ℝ≥0) :
    IdentDistrib (fun x : Paths d => fun i => x i t) (observation t)
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
  (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    ⟨(measurable_observation t).aemeasurable, rfl⟩

theorem lintegral_response_row_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∫⁻ x, ∑' v, ENNReal.ofReal (response beta u v t x ^ 2) ∂observationLaw μ) ≤
      ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t) := by
  have hg := hμ.infiniteGibbsResponse_critical_row_energy hb hd hc ht u
  simp only [infiniteGibbsResponseRow] at hg
  have he := (observation_snapshot_identDistrib (μ := μ) t).comp
    (show Measurable (fun y : TreeVertex d → ℝ => ∑' v : TreeVertex d,
      ENNReal.ofReal (infiniteGibbsResponse beta u v y ^ 2)) from
      Measurable.tsum (fun v =>
        ((measurable_infiniteGibbsResponse beta u v).pow_const 2).ennreal_ofReal))
  have hs := hg.1.mono fun p hp => ENNReal.ofReal_tsum_of_nonneg
    (fun v => sq_nonneg (infiniteGibbsResponse beta u v (observation t p))) hp
  change (∫⁻ x, (fun y => ∑' v, ENNReal.ofReal
    (infiniteGibbsResponse beta u v y ^ 2)) (fun i => x i t) ∂observationLaw μ) ≤ _
  have heq := he.lintegral_eq
  dsimp only [Function.comp_def] at heq
  rw [heq, ← lintegral_congr_ae hs,
    ← ofReal_integral_eq_lintegral_ofReal hg.2.1
      (Eventually.of_forall fun p => tsum_nonneg (fun v => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hg.2.2

theorem response_row_energy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Summable (fun v => response beta u v t x ^ 2)) ∧
    Integrable (fun x => ∑' v, response beta u v t x ^ 2) (observationLaw μ) ∧
    (∫ x, ∑' v, response beta u v t x ^ 2 ∂observationLaw μ) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  have hg := hμ.infiniteGibbsResponse_critical_row_energy hb hd hc ht u
  simp only [infiniteGibbsResponseRow] at hg
  have he := (observation_snapshot_identDistrib (μ := μ) t).comp
    (measurable_infiniteGibbsResponseRow beta u)
  refine ⟨?_, he.integrable_iff.mpr hg.2.1, he.integral_eq.trans_le hg.2.2⟩
  have hfin := (lintegral_response_row_le hμ hb hd hc ht u).trans_lt ENNReal.ofReal_lt_top
  have hm : Measurable (fun x : Paths d => ∑' v,
      ENNReal.ofReal (response beta u v t x ^ 2)) :=
    Measurable.tsum fun v => ((measurable_response beta u v t).pow_const 2).ennreal_ofReal
  filter_upwards [ae_lt_top' hm.aemeasurable hfin.ne] with x hx
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hx.ne

def copyObservation (j : Bool) (q : Paths d × (Paths d × Paths d)) : Paths d :=
  if j then q.2.2 else q.2.1

theorem measurePreserving_copyObservation (j : Bool) :
    MeasurePreserving (copyObservation (d := d) j) (copies beta μ) (observationLaw μ) := by
  cases j
  · exact IsingCopyStationarity.measurePreserving_observations.1
  · exact IsingCopyStationarity.measurePreserving_observations.2

theorem copy_response_row_energy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) (j : Bool) :
    (∀ᵐ q ∂copies beta μ,
      Summable (fun v => response beta u v t (copyObservation j q) ^ 2)) ∧
    Integrable (fun q => ∑' v, response beta u v t (copyObservation j q) ^ 2)
      (copies beta μ) ∧
    (∫ q, ∑' v, response beta u v t (copyObservation j q) ^ 2 ∂copies beta μ) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  have h := response_row_energy hμ hb hd hc ht u
  have hp := measurePreserving_copyObservation (beta := beta) (μ := μ) j
  exact ⟨hp.quasiMeasurePreserving.ae h.1, hp.integrable_comp_of_integrable h.2.1,
    (hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2⟩

theorem difference_response_row_energy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∀ᵐ q ∂copies beta μ,
      Summable (fun v => (response beta u v t q.2.1 - response beta u v t q.2.2) ^ 2)) ∧
    Integrable (fun q => ∑' v,
      (response beta u v t q.2.1 - response beta u v t q.2.2) ^ 2) (copies beta μ) ∧
    (∫ q, ∑' v, (response beta u v t q.2.1 - response beta u v t q.2.2) ^ 2
      ∂copies beta μ) ≤ 4 * (1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t) := by
  have hl := copy_response_row_energy hμ hb hd hc ht u false
  have hr := copy_response_row_energy hμ hb hd hc ht u true
  simp only [copyObservation, Bool.false_eq_true, ite_false, ite_true] at hl hr
  have hs := hl.1.and hr.1
  have hi := DiscrepancyEnergy.integrable_sq_difference_row
    (fun v => ((measurable_response beta u v t).comp
      (measurable_fst.comp measurable_snd)).aestronglyMeasurable)
    (fun v => ((measurable_response beta u v t).comp
      (measurable_snd.comp measurable_snd)).aestronglyMeasurable) hl.2.1 hr.2.1 hs
  refine ⟨hs.mono (fun q hq => DiscrepancyEnergy.summable_sq_sub hq.1 hq.2), hi, ?_⟩
  calc
    _ ≤ ∫ q, 2 * ((∑' v, response beta u v t q.2.1 ^ 2) +
        ∑' v, response beta u v t q.2.2 ^ 2) ∂copies beta μ := by
      apply integral_mono_ae hi ((hl.2.1.add hr.2.1).const_mul 2)
      exact hs.mono fun q hq => DiscrepancyEnergy.tsum_sq_sub_le hq.1 hq.2
    _ = 2 * ((∫ q, ∑' v, response beta u v t q.2.1 ^ 2 ∂copies beta μ) +
        ∫ q, ∑' v, response beta u v t q.2.2 ^ 2 ∂copies beta μ) := by
      rw [integral_const_mul, integral_add hl.2.1 hr.2.1]
    _ ≤ _ := by linarith [hl.2.2, hr.2.2]

end Problem367.IsingObservationResponseEnergy

end

end OAI
