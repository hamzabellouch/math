import OAI.Probability.FreeIsing.Ising.CanonicalContinuousFields
import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

private lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_tanh_response z).continuousAt)

def siteRootResponse (hb : 0 ≤ beta) (v : TreeVertex d)
    (H : TreeVertex d → ℝ) : ℝ :=
  Real.tanh beta ^ v.1.length *
    ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i))

lemma continuous_siteRootResponse (hb : 0 ≤ beta) (v : TreeVertex d) :
    Continuous (siteRootResponse hb v) := by
  unfold siteRootResponse
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro i hi
  exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).comp
    (continuous_fst.comp ((continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)).comp
      ((continuous_apply _).prodMk (continuous_apply _))))

lemma siteRootResponse_mem_Icc (hb : 0 ≤ beta) (v : TreeVertex d)
    (H : TreeVertex d → ℝ) :
    0 ≤ siteRootResponse hb v H ∧ siteRootResponse hb v H ≤ 1 := by
  have hp0 : 0 ≤ ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i)) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  have hp1 : (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i))) ≤ 1 :=
    Finset.prod_le_one₀
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)
  have ht0 := pow_nonneg (tanh_nonneg_of_beta_nonneg hb) v.1.length
  have ht1 : Real.tanh beta ^ v.1.length ≤ 1 :=
    pow_le_one₀ (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta).le
  exact ⟨mul_nonneg ht0 hp0, (mul_le_mul ht1 hp1 hp0 (by norm_num)).trans_eq (one_mul 1)⟩

def continuousRootResponse (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  siteRootResponse hb v (fun i => continuousField beta i t x)

lemma continuousRootResponse_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootResponse hb v) := by
  intro t
  let : MeasurableSpace (Paths d) := filtration d t
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun i => (continuousField_progressive beta i t).measurable))).stronglyMeasurable

lemma continuousRootResponse_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootResponse hb v t x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := siteRootResponse_mem_Icc hb v (fun i => continuousField beta i t x)
  exact (abs_of_nonneg h0).trans_le h1

theorem continuousRootResponse_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootResponse hb v t x) := by
  have hc (i : TreeVertex d) := (continuousField_modification hd hμ hb hcrit i).1
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact (continuous_siteRootResponse hb v).comp (continuous_pi hx)

theorem continuousRootResponse_eq_response_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    continuousRootResponse hb v t =ᵐ[observationLaw μ]
      fun x => infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => x i t) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he (i : TreeVertex d) := (continuousField_modification hd hμ hb hcrit i).2 t
  filter_upwards [ae_all_iff.mpr he,
    IsingCopyResponseRowPaths.row_eq_product_ae hμ hb t v] with x hx hr
  change siteRootResponse hb v (fun i => continuousField beta i t x) = _
  rw [show (fun i => continuousField beta i t x) = (fun i => field beta i t x)
    from funext hx]
  exact hr.symm

def continuousRootCovariance (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  (1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2) *
    continuousRootResponse hb v t x

lemma continuousRootCovariance_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootCovariance hb v) := by
  intro t
  have hf := continuousField_progressive beta (ConnectedHull.root d) t
  exact (stronglyMeasurable_const.sub
    ((continuous_tanh.comp_stronglyMeasurable hf).pow 2)).mul
      (continuousRootResponse_progressive hb v t)

lemma continuousRootCovariance_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootCovariance hb v t x| ≤ 1 := by
  have h0 := (sub_pos.mpr (Real.tanh_sq_lt_one
    (continuousField beta (ConnectedHull.root d) t x))).le
  have h1 : 1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2 ≤ 1 :=
    sub_le_self _ (sq_nonneg _)
  rw [continuousRootCovariance, abs_mul, abs_of_nonneg h0]
  exact (mul_le_mul h1 (continuousRootResponse_abs_le_one hb v t x)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem continuousRootCovariance_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootCovariance hb v t x) := by
  filter_upwards [(continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousRootResponse_continuous_ae hd hμ hb hcrit v] with x hf hr
  exact (continuous_const.sub ((continuous_tanh.comp hf).pow 2)).mul hr

theorem continuousRootCovariance_eq_covariance_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    continuousRootCovariance hb v t =ᵐ[observationLaw μ]
      fun x => infiniteGibbsCovariance beta (ConnectedHull.root d) v (fun i => x i t) := by
  filter_upwards [(continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).2 t,
    continuousRootResponse_eq_response_ae hd hμ hb hcrit v t,
    tanh_field_eq_posterior_ae hμ hb (ConnectedHull.root d) t,
    posterior_mem_Ioo_ae hμ hb (ConnectedHull.root d) t] with x hf hr hm hi
  have hpos : 0 < 1 - posterior beta (ConnectedHull.root d) t x ^ 2 := by
    nlinarith [hi.1, hi.2]
  rw [continuousRootCovariance, hf, hm, hr, infiniteGibbsResponse]
  change (1 - posterior beta (ConnectedHull.root d) t x ^ 2) *
    (_ / (1 - posterior beta (ConnectedHull.root d) t x ^ 2)) = _
  exact mul_div_cancel₀ _ hpos.ne'

end Problem367.IsingObservationFactor

end

end OAI
