import OAI.Probability.FreeIsing.Cavity.Array
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Posterior.FieldL2Limit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

local instance : Nonempty IsingSpin := ⟨.neg⟩

def finiteSiteField {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (v : D) (y : TreeVertex d → ℝ) : ℝ :=
  Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) (D.restrict y))

private theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem measurable_finiteSiteField {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) : Measurable (finiteSiteField beta D v) :=
  measurable_artanh.comp ((FinitePosterior.continuous_fieldMean _ _ _).measurable.comp
    D.measurable_restrict)

def finiteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v w : D) (y : TreeVertex d → ℝ) : ℝ :=
  (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (finiteSiteField beta D v y, finiteSiteField beta D w y)).1

def infiniteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v w : TreeVertex d) (y : TreeVertex d → ℝ) : ℝ :=
  CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (fun u => Real.artanh (infiniteGibbsSpinMean beta u y)) v w

theorem measurable_finiteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v w : D) :
    Measurable (finiteCavityField hbeta D v w) :=
  measurable_fst.comp ((measurable_cavityFromSites _ _).comp
    ((measurable_finiteSiteField beta D v).prodMk (measurable_finiteSiteField beta D w)))

theorem measurable_infiniteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v w : TreeVertex d) : Measurable (infiniteCavityField hbeta v w) := by
  exact (CavityArray.measurable_field_apply _ _ v w).comp
    (Measurable.of_eval (fun u => measurable_artanh.comp
      (measurable_infiniteGibbsSpinMean beta u)))

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.exhaustionSiteField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n))
    (hex : ∀ u, ∃ n, u ∈ D n) (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteSiteField beta (D n) ⟨v, hv n⟩ (observation t p))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v (observation t p)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  have hce (n : ℕ) := hμ.finiteObservation_condExp (D n) (hconn n) t
    (fun eta => spinSign (eta ⟨v, hv n⟩))
  filter_upwards [hlim, ae_all_iff.mpr hce,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp hce hinf
  convert hp.2.2 using 1
  · ext n
    exact congrArg Real.artanh (hce n).symm
  · exact congrArg (fun x : ℝ => 𝓝 (Real.artanh x)) hinf

theorem HasFreeIsingLaw.exhaustionSiteField_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n))
    (hex : ∀ u, ∃ n, u ∈ D n) (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ p,
      (finiteSiteField beta (D n) ⟨v, hv n⟩ (observation t p) -
        Real.artanh (infiniteGibbsSpinMean beta v (observation t p))) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_integral_sq_sub_posterior_fields
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  convert hlim using 1
  ext n
  apply integral_congr_ae
  filter_upwards [hμ.finiteObservation_condExp (D n) (hconn n) t
    (fun eta => spinSign (eta ⟨v, hv n⟩)),
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hfinite hinf
  change _ = (Real.artanh (_) - Real.artanh
    (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)) ^ 2
  rw [hinf]
  congr 2
  exact congrArg Real.artanh hfinite.symm

theorem HasFreeIsingLaw.exhaustionCavityField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v w : TreeVertex d) (hv : ∀ n, v ∈ D n) (hw : ∀ n, w ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩
        (observation t p)) atTop (𝓝 (infiniteCavityField hbeta v w (observation t p))) := by
  filter_upwards [hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex v hv t,
    hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex w hw t] with p hp hq
  exact (continuous_fst.comp (continuous_cavityFromSites
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hp.prodMk_nhds hq)

theorem HasFreeIsingLaw.exhaustionCavityField_discrepancy_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v w : D) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |finiteCavityField hbeta D v w (observation t p) -
        infiniteCavityField hbeta v.1 w.1 (observation t p)| ≤
      (2 * ((d : ℝ) * beta)) / (1 - Real.tanh beta) := by
  filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v.1,
    hμ.gaussian_posterior_field_bound hbeta t w.1,
    hμ.infiniteGibbsSpinMean_eq_posterior t v.1,
    hμ.infiniteGibbsSpinMean_eq_posterior t w.1] with p hbv hbw hev hew
  let y := observation t p
  have hb (u : D) (hu : |Real.artanh (infiniteGibbsSpinMean beta u.1 y) - y u.1| ≤
      (d : ℝ) * beta) :
      |finiteSiteField beta D u y - Real.artanh (infiniteGibbsSpinMean beta u.1 y)| ≤
        2 * ((d : ℝ) * beta) := by
    have hf := finite_tree_gibbs_field_uniform_bound D hbeta (D.restrict y) u
    change |finiteSiteField beta D u y - y u.1| ≤ (d : ℝ) * beta at hf
    calc
      _ = |(finiteSiteField beta D u y - y u.1) -
        (Real.artanh (infiniteGibbsSpinMean beta u.1 y) - y u.1)| := by congr 1; ring
      _ ≤ |finiteSiteField beta D u y - y u.1| +
        |Real.artanh (infiniteGibbsSpinMean beta u.1 y) - y u.1| := abs_sub _ _
      _ ≤ _ := by linarith
  have hv := hb v (by simpa only [y, hev] using hbv.2)
  have hw := hb w (by simpa only [y, hew] using hbw.2)
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  have hs := cavityFromSites_spec h0 h1 (finiteSiteField beta D v y, finiteSiteField beta D w y)
  have hs' := cavityFromSites_spec h0 h1
    (Real.artanh (infiniteGibbsSpinMean beta v.1 y), Real.artanh (infiniteGibbsSpinMean beta w.1 y))
  exact cavity_pair_sub_abs_le h0 h1 hs.1 hs.2 hs'.1 hs'.2 hv hw

theorem HasFreeIsingLaw.exhaustionCavityField_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v w : TreeVertex d) (hv : ∀ n, v ∈ D n) (hw : ∀ n, w ∈ D n)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ p,
      (finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩ (observation t p) -
        infiniteCavityField hbeta v w (observation t p)) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hm (n : ℕ) := ((measurable_finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩).comp
    (measurable_observation t)).sub ((measurable_infiniteCavityField hbeta v w).comp
      (measurable_observation t))
  have hbound (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      ‖(finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩ (observation t p) -
        infiniteCavityField hbeta v w (observation t p)) ^ 2‖ ≤
        ((2 * ((d : ℝ) * beta)) / (1 - Real.tanh beta)) ^ 2 := by
    filter_upwards [hμ.exhaustionCavityField_discrepancy_bound hbeta (D n)
      ⟨v, hv n⟩ ⟨w, hw n⟩ t] with p hp
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hzero := hμ.exhaustionCavityField_tendsto_ae hbeta D hD hconn hex v w hv hw t
  have hlim := tendsto_integral_of_dominated_convergence
    (fun _ => ((2 * ((d : ℝ) * beta)) / (1 - Real.tanh beta)) ^ 2)
    (fun n => (hm n).aestronglyMeasurable.pow 2) (integrable_const _) hbound
    (hzero.mono (fun p hp => by simpa using
      (hp.sub_const (infiniteCavityField hbeta v w (observation t p))).pow 2))
  simpa using hlim

end Problem367

end

end OAI
