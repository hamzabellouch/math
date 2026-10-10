import OAI.Probability.FreeIsing.Critical.CanonicalRowEnergy
import OAI.Probability.FreeIsing.Posterior.ArrayPosteriorCovarianceStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry CriticalCanonicalRowEnergy

theorem HasFreeIsingLaw.gaussian_posteriorResponse_relabel_ae
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (t : ℝ≥0) (g : TreeAut d)
    (u v : TreeVertex d) :
    gaussianPosteriorResponse μ t u v ∘ Prod.map (relabel g) (relabel g) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      gaussianPosteriorResponse μ t (g.toEquiv.symm u) (g.toEquiv.symm v) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hfield : (observationSigma (TreeVertex d) (t : ℝ)).comap
      (Prod.map (relabel g) (relabel g)) = observationSigma (TreeVertex d) (t : ℝ) := by
    change (selectedObservationField F id).comap
      (Prod.map (relabel g) (relabel g)) = selectedObservationField F id
    rw [selectedObservationField_comap_relabel]
    apply selectedObservationField_eq_of_range_eq
    simp only [id_eq, Equiv.range_eq_univ, Set.range_id]
  have hs : Measurable spinSign := by intro s hs; trivial
  have hm (w : TreeVertex d) : Measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => spinSign (p.1 w)) :=
    hs.comp ((measurable_pi_apply w).comp measurable_fst)
  have h := posteriorResponse_comp_measurePreserving
    (PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g)
    (hm u) (hm v) (integrable_plantedSpin _ u) (integrable_plantedSpin _ v)
    (ArrayPosteriorStationarity.integrable_spin_pair _ u v)
    (observationSigma_le (TreeVertex d) (t : ℝ))
  rw [hfield] at h
  exact h.symm

theorem HasFreeIsingLaw.gaussian_response_critical_intrinsic_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u v : TreeVertex d) :
    (∫ p, gaussianPosteriorResponse μ t u v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * Real.exp (-rate beta t)) ^ reducedWordDistance u.1 v.1 := by
  obtain ⟨g, hgu, hdist⟩ := exists_treeAut_to_root_distance u
  change g.toEquiv u = ConnectedHull.root d at hgu
  have hsu : g.toEquiv.symm (ConnectedHull.root d) = u := by
    rw [← hgu, Equiv.symm_apply_apply]
  have hn := hμ.gaussian_posteriorResponse_relabel_ae t g (ConnectedHull.root d) (g.toEquiv v)
  simp only [hsu, Equiv.symm_apply_apply] at hn
  have hmp : MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hi := (hμ.gaussian_posteriorResponse_sq_decay hb ht
    (ConnectedHull.root d) (g.toEquiv v) rfl).1
  calc
    _ = ∫ p, gaussianPosteriorResponse μ t (ConnectedHull.root d) (g.toEquiv v)
        (Prod.map (relabel g) (relabel g) p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) :=
      integral_congr_ae (hn.symm.fun_comp (fun x : ℝ => x ^ 2))
    _ = ∫ p, gaussianPosteriorResponse μ t (ConnectedHull.root d) (g.toEquiv v) p ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) :=
      hmp.hasLaw.integral_comp hi.aestronglyMeasurable
    _ ≤ _ := by
      simpa only [hdist] using
        hμ.gaussian_rootResponse_critical_radial_bound hb hd hc ht (g.toEquiv v)

theorem HasFreeIsingLaw.gaussian_response_critical_row_energy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => gaussianPosteriorResponse μ t u v p ^ 2)) ∧
    Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t u v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, gaussianPosteriorResponse μ t u v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  obtain ⟨g, hgu⟩ := exists_treeAut_to_root u
  change g.toEquiv u = ConnectedHull.root d at hgu
  have hsu : g.toEquiv.symm (ConnectedHull.root d) = u := by
    rw [← hgu, Equiv.symm_apply_apply]
  have hn := ae_all_iff.mpr (fun v =>
    hμ.gaussian_posteriorResponse_relabel_ae t g (ConnectedHull.root d) v)
  simp only [hsu] at hn
  have hmp : MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hg := hμ.gaussian_rootResponse_critical_row_energy hb hd hc ht
  have he : (fun p => ∑' v,
      gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2) ∘
        Prod.map (relabel g) (relabel g) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => ∑' v, gaussianPosteriorResponse μ t u v p ^ 2 := by
    filter_upwards [hn] with p hp
    change (∑' v, gaussianPosteriorResponse μ t (ConnectedHull.root d) v
      (Prod.map (relabel g) (relabel g) p) ^ 2) = _
    exact (tsum_congr (fun v => congrArg (fun x : ℝ => x ^ 2) (hp v))).trans
      (g.toEquiv.symm.tsum_eq (fun v => gaussianPosteriorResponse μ t u v p ^ 2))
  refine ⟨?_, (hmp.integrable_comp_of_integrable hg.2.1).congr he, ?_⟩
  · filter_upwards [hmp.quasiMeasurePreserving.ae hg.1, hn] with p hp hnat
    exact g.toEquiv.symm.summable_iff.mp
      (hp.congr (fun v => congrArg (fun x : ℝ => x ^ 2) (hnat v)))
  · rw [← integral_congr_ae he, hmp.hasLaw.integral_comp hg.2.1.aestronglyMeasurable]
    exact hμ.integral_gaussian_rootResponse_row_le_inv_rate hb hd hc ht

theorem HasFreeIsingLaw.infiniteGibbsResponse_eq_gaussian_response
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (u v : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta u v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)] gaussianPosteriorResponse μ t u v := by
  filter_upwards [hμ.infiniteGibbsCovariance_eq_posterior t u v,
    hμ.infiniteGibbsSpinMean_eq_posterior t u] with p hc hm
  unfold infiniteGibbsResponse gaussianPosteriorResponse posteriorResponse
  rw [hc, hm]
  rfl

theorem HasFreeIsingLaw.infiniteGibbsResponse_critical_row_energy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => infiniteGibbsResponse beta u v (observation t p) ^ 2)) ∧
    Integrable (fun p => infiniteGibbsResponseRow beta u (observation t p))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, infiniteGibbsResponseRow beta u (observation t p)
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  have hg := hμ.gaussian_response_critical_row_energy hb hd hc ht u
  have hn := ae_all_iff.mpr (fun v => hμ.infiniteGibbsResponse_eq_gaussian_response t u v)
  have he : (fun p => infiniteGibbsResponseRow beta u (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => ∑' v, gaussianPosteriorResponse μ t u v p ^ 2 := by
    filter_upwards [hn] with p hp
    exact tsum_congr fun v => congrArg (fun x : ℝ => x ^ 2) (hp v)
  refine ⟨?_, hg.2.1.congr he.symm, ?_⟩
  · filter_upwards [hg.1, hn] with p hp hnat
    exact hp.congr fun v => congrArg (fun x : ℝ => x ^ 2) (hnat v).symm
  · rw [integral_congr_ae he]
    exact hg.2.2

theorem HasFreeIsingLaw.brownian_response_critical_row_energy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) {t : ℝ≥0} (ht : 0 < t) (u : TreeVertex d) :
    (∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Summable (fun v => brownianPosteriorResponse μ ν B t u v p ^ 2)) ∧
    Integrable (fun p => ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2)
      (μ.prod (Measure.infinitePi ν)) ∧
    (∫ p, ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  have hg := hμ.gaussian_response_critical_row_energy hb hd hc ht u
  have heq := ae_all_iff.mpr (fun v =>
    brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t u v)
  have he : (fun p => ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2) =ᵐ[
      μ.prod (Measure.infinitePi ν)]
      (fun q => ∑' v, gaussianPosteriorResponse μ t u v q ^ 2) ∘
        Prod.map id (fun p i => B i t (p i)) := by
    filter_upwards [heq] with p hp
    exact tsum_congr fun v => congrArg (fun x : ℝ => x ^ 2) (hp v)
  refine ⟨?_, (hT.integrable_comp_of_integrable hg.2.1).congr he.symm, ?_⟩
  · filter_upwards [hT.quasiMeasurePreserving.ae hg.1, heq] with p hp hpeq
    exact hp.congr fun v => congrArg (fun x : ℝ => x ^ 2) (hpeq v).symm
  · rw [integral_congr_ae he, hT.hasLaw.integral_comp hg.2.1.aestronglyMeasurable]
    exact hg.2.2

end Problem367

end

end OAI
