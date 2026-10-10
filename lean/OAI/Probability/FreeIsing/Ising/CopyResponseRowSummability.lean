import OAI.Probability.FreeIsing.Gaussian.TreeResponseObservedPosterior
import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem row_identDistrib_gaussian
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    IdentDistrib (row beta t v)
      (gaussianPosteriorResponse μ t (ConnectedHull.root d) v)
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have hr := hobs.comp (measurable_infiniteGibbsResponse beta (ConnectedHull.root d) v)
  have heq := (hμ.infiniteGibbsRootResponse_eq_canonical_product hb t v).trans
    (hμ.gaussian_rootResponse_eq_canonical_product hb t v).symm
  exact hr.trans (IdentDistrib.of_ae_eq hr.aemeasurable_snd heq)

theorem integrable_row_sq_and_integral_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    Integrable (fun x => row beta t v x ^ 2) (observationLaw μ) ∧
      (∫ x, row beta t v x ^ 2 ∂observationLaw μ) ≤
        (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  have hi := (row_identDistrib_gaussian hμ hb t v).sq
  have hg := hμ.gaussian_posteriorResponse_sq_decay hb ht (ConnectedHull.root d) v rfl
  exact ⟨hi.integrable_iff.mpr hg.1, hi.integral_eq.trans_le hg.2⟩

theorem observation_row_energy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    (∀ᵐ x ∂observationLaw μ, Summable (fun v => row beta t v x ^ 2)) ∧
      Integrable (fun x => ∑' v, row beta t v x ^ 2) (observationLaw μ) ∧
      (∫ x, ∑' v, row beta t v x ^ 2 ∂observationLaw μ) ≤
        1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) /
          (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  have hc := integrable_row_sq_and_integral_le hμ hb ht
  have hnonneg := mul_nonneg (sq_nonneg (Real.tanh beta)) (gaussianContraction_pos beta t).le
  have hsmall := gaussian_radial_ratio_lt_one ht hcrit
  have hs : Summable (fun v => ∫ x, row beta t v x ^ 2 ∂observationLaw μ) :=
    summable_of_tree_radial_le (C := 1)
      (fun v => integral_nonneg (fun x => sq_nonneg _))
      (fun v => by simpa only [one_mul] using (hc v).2) hnonneg hsmall
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun v => (hc v).1) hs
  refine ⟨hae, hint, ?_⟩
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound (C := 1)
    (fun v => (hc v).1) (fun v => by simpa only [one_mul] using (hc v).2) hnonneg hsmall

theorem copies_rows_summable_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∀ᵐ q ∂copies beta μ,
      Summable (fun v => row beta t v q.2.1 ^ 2) ∧
        Summable (fun v => row beta t v q.2.2 ^ 2) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hrow := (observation_row_energy hμ hb ht hcrit).1
  filter_upwards [hl.quasiMeasurePreserving.ae hrow,
    hr.quasiMeasurePreserving.ae hrow] with q hqL hqR
  exact ⟨hqL, hqR⟩

theorem integrable_copies_row_energies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    Integrable (fun q => ∑' v, row beta t v q.2.1 ^ 2) (copies beta μ) ∧
      Integrable (fun q => ∑' v, row beta t v q.2.2 ^ 2) (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hrow := (observation_row_energy hμ hb ht hcrit).2.1
  exact ⟨hl.integrable_comp_of_integrable hrow, hr.integrable_comp_of_integrable hrow⟩

theorem integral_density_le_shell_energies_of_positive
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {Q L : ℕ → ℝ} (hQ0 : ∀ n, 0 ≤ Q n) (hL0 : ∀ n, 0 ≤ L n)
    (hQ : ∀ n (v : TreeVertex d), v.1.length = n + 1 → noiseEnergy (μ := μ) hb t v ≤ Q n)
    (hL : ∀ n (v : TreeVertex d), v.1.length = n + 1 → linearEnergy (μ := μ) hb t v ≤ L n)
    (hQs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * Q n))
    (hLs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * L n))
    (hRs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * Real.sqrt (Q n))) :
    let U := IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t
    let D := DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) U
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.1))
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.2))
    Integrable D (copies beta μ) ∧
      (∫ q, D q ∂copies beta μ) ≤ 2 * (∫ q, U q ^ 2 ∂copies beta μ) +
        ∑' n, regularPathWeight d (Real.tanh beta) n *
          (Q n + 2 * L n + 4 * Real.sqrt (2 * ∫ q, U q ^ 2 ∂copies beta μ) * Real.sqrt (Q n)) :=
  integral_density_le_shell_energies hμ hb t hQ0 hL0 hQ hL hQs hLs hRs
    (copies_rows_summable_ae hμ hb ht hcrit)

end Problem367.IsingCopyResponseRowPaths

end

end OAI
