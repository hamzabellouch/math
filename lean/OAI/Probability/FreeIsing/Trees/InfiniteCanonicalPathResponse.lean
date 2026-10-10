import OAI.Probability.FreeIsing.Brownian.ResponseTransport
import OAI.Probability.FreeIsing.Cavity.FieldL2Limit
import OAI.Probability.FreeIsing.Energy.ProgressiveIsingCovariance
import OAI.Probability.FreeIsing.Energy.ShiftedFieldVariance
import OAI.Probability.FreeIsing.Gaussian.TreeResponsePosterior
import OAI.Probability.FreeIsing.Posterior.NormalizedPosteriorLimit
import OAI.Probability.FreeIsing.Trees.CanonicalPathResponse

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

theorem finiteSiteField_eq_treeField {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = TreePathResponse.field beta y D v.1 := by
  unfold finiteSiteField TreePathResponse.field TreePathResponse.mean
  rw [GibbsLeaf.expectation_eq_fieldMean]
  simp only [extendFiniteSpin_apply D _ v]

def rootResponseProduct {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (y : TreeVertex d → ℝ) : ℝ :=
  Real.tanh beta ^ v.1.length *
    ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (infiniteCavityField hbeta (ConnectedHull.takeVertex v (i + 1))
        (ConnectedHull.takeVertex v i) y)

theorem infiniteCavityField_eq_snd {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (u v : TreeVertex d) (y : TreeVertex d → ℝ) :
    infiniteCavityField hbeta v u y =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (infiniteGibbsSpinMean beta u y),
          Real.artanh (infiniteGibbsSpinMean beta v y))).2 :=
  CavityArray.field_reverse _ _ _ u v

theorem measurable_rootResponseProduct {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v : TreeVertex d) : Measurable (rootResponseProduct hbeta v) := by
  unfold rootResponseProduct
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i hi
  exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
    (measurable_infiniteCavityField hbeta _ _)

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.gaussian_rootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    gaussianPosteriorResponse μ t (ConnectedHull.root d) v =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  classical
  let D := connectedExhaustion v
  have hpath (i : ℕ) (hi : i ≤ v.1.length) (n : ℕ) :
      ConnectedHull.takeVertex v i ∈ D n := by
    exact ConnectedHull.prefix_mem_hull (Finset.mem_insert_self v (treeBallFinset d n)) hi
  have hr (n : ℕ) : ConnectedHull.root d ∈ D n := by
    simpa only [ConnectedHull.prefix_zero] using hpath 0 (Nat.zero_le _) n
  have hv (n : ℕ) : v ∈ D n := mem_connectedExhaustion v n
  have hconn (n : ℕ) : ConnectedFinset (D n) := connectedExhaustion_connected v n
  have hex (u : TreeVertex d) : ∃ n, u ∈ D n :=
    (eventually_mem_connectedExhaustion v u).exists
  have hfield (i : Fin (v.1.length + 1)) :
      ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
        Tendsto (fun n => TreePathResponse.field beta (observation t p) (D n)
          (ConnectedHull.takeVertex v i)) atTop
          (𝓝 (Real.artanh (infiniteGibbsSpinMean beta
            (ConnectedHull.takeVertex v i) (observation t p)))) := by
    have hh := hμ.exhaustionSiteField_tendsto_ae hbeta D
      (connectedExhaustion_monotone v) hconn hex (ConnectedHull.takeVertex v i)
      (hpath i (by omega)) t
    simpa only [finiteSiteField_eq_treeField] using hh
  have hprod : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (TreePathResponse.orientedCavity hbeta (observation t p) (D n)
            (ConnectedHull.takeVertex v i) (ConnectedHull.takeVertex v (i + 1))))
        atTop (𝓝 (rootResponseProduct hbeta v (observation t p))) := by
    filter_upwards [ae_all_iff.mpr hfield] with p hp
    apply Tendsto.const_mul
    apply tendsto_finsetProd
    intro i hi
    have hi' : i < v.1.length := Finset.mem_range.mp hi
    have hleft := hp ⟨i, by omega⟩
    have hright := hp ⟨i + 1, by omega⟩
    have hc := (continuous_snd.comp (continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hleft.prodMk_nhds hright)
    simp only [Function.comp_apply] at hc
    rw [← infiniteCavityField_eq_snd hbeta] at hc
    exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).continuousAt.tendsto.comp hc
  have hresponse := hμ.gaussian_posteriorResponse_tendsto_ae hbeta D
    (connectedExhaustion_monotone v) hex t (ConnectedHull.root d) v
  have hfinite (n : ℕ) := hμ.finiteObservation_normalizedResponse
    (D n) (hconn n) t ⟨ConnectedHull.root d, hr n⟩ ⟨v, hv n⟩
  filter_upwards [hresponse, hprod, ae_all_iff.mpr hfinite] with p hp hprod hfinite
  apply tendsto_nhds_unique hp
  apply hprod.congr'
  apply Eventually.of_forall
  intro n
  exact (hfinite n).trans
    (TreePathResponse.root_response_eq_canonical_product hbeta (observation t p)
      (hconn n) (hr n) (hv n)) |>.symm

theorem HasFreeIsingLaw.infiniteGibbsRootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta (ConnectedHull.root d) v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  filter_upwards [hμ.gaussian_rootResponse_eq_canonical_product hbeta t v,
    hμ.infiniteGibbsCovariance_eq_posterior t (ConnectedHull.root d) v,
    hμ.infiniteGibbsSpinMean_eq_posterior t (ConnectedHull.root d)] with p hp hc hm
  rw [infiniteGibbsResponse, hc, hm]
  exact hp

theorem HasFreeIsingLaw.infiniteGibbsRootResponse_brownian_eq_canonical_product
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsResponse beta (ConnectedHull.root d) v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
      μ.prod (Measure.infinitePi ν)]
      fun p => rootResponseProduct hbeta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  exact hT.quasiMeasurePreserving.ae
    (hμ.infiniteGibbsRootResponse_eq_canonical_product hbeta t v)

theorem HasFreeIsingLaw.brownian_past_rootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    posteriorResponse (μ.prod (Measure.infinitePi ν))
      (MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance)
      (fun p => spinSign (p.1 (ConnectedHull.root d))) (fun p => spinSign (p.1 v)) =ᵐ[
      μ.prod (Measure.infinitePi ν)]
      fun p => rootResponseProduct hbeta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  exact (brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t
    (ConnectedHull.root d) v).trans (hT.quasiMeasurePreserving.ae
      (hμ.gaussian_rootResponse_eq_canonical_product hbeta t v))

end Problem367

end

end OAI
