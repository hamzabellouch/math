import OAI.Probability.SLE.HausdorffLimits

namespace OAI

/-!
The deterministic comparison behind Corollary `cor:larger-gauge` in
*An explicit exact Hausdorff gauge for SLE* (26 September 2026).

The Hausdorff measures here are the existing `Measure.mkMetric` constructions, so
the comparison applies to arbitrary countable spatial covers. No SLE estimate is
assumed in the comparison theorem: positive measure for the smaller gauge is the
sole input to the non-sigma-finiteness conclusion.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

lemma logLog_inv_tendsto_atTop :
    Tendsto (fun r : ℝ => Real.log (Real.log (1 / r))) (𝓝[>] 0) atTop := by
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)

/-- The regular exact gauge is asymptotically smaller than Schramm's proposed
exponent-one log-log gauge. -/
theorem hFormula_div_gFormula_tendsto_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun r => hFormula κ r / gFormula κ r) (𝓝[>] 0) (𝓝 0) := by
  have hq : 0 < 1 - codimension κ / 2 := by
    dsimp [codimension, dimension]
    linarith
  have ht := (tendsto_rpow_neg_atTop hq).comp logLog_inv_tendsto_atTop
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    logLog_inv_tendsto_atTop.eventually (eventually_gt_atTop 0)] with r hr hl
  have hrp : 0 < r := hr
  have hrpow : r ^ dimension κ ≠ 0 := (Real.rpow_pos_of_pos hrp _).ne'
  dsimp only [Function.comp_def, hFormula, gFormula]
  rw [mul_div_mul_left _ _ hrpow, ← Real.rpow_sub_one hl.ne']
  congr 1
  ring

theorem gauge_ratio_tendsto_zero {κ : ℝ} (hκ : 0 < κ)
    {h g : ℝ → ℝ} (hf : HasSmallRadiusFormula h (hFormula κ))
    (gf : HasSmallRadiusFormula g (gFormula κ)) :
    Tendsto (fun r => h r / g r) (𝓝[>] 0) (𝓝 0) := by
  apply (hFormula_div_gFormula_tendsto_zero hκ).congr'
  exact (hf.div gf).symm

/-- A small-radius ratio estimate gives a comparison of the associated
Hausdorff measures, independently of their values at large radii. -/
theorem hausdorffGauge_le_smul_of_ratio_tendsto_zero
    {h g : ℝ → ℝ} (hh : IsGauge h) (hg : IsGauge g)
    (hratio : Tendsto (fun r => h r / g r) (𝓝[>] 0) (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    hausdorffGauge h ≤ ENNReal.ofReal c • hausdorffGauge g := by
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), h r / g r < c :=
    hratio.eventually (gt_mem_nhds hc)
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have htoReal : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ)) := by
    simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top
  have hevent : ∀ᶠ r : ℝ≥0∞ in 𝓝 (0 : ℝ≥0∞),
      extendedGauge h r ≤ ENNReal.ofReal c * extendedGauge g r := by
    filter_upwards [htoReal.eventually (gt_mem_nhds hδ)] with r hr
    by_cases hz : r.toReal = 0
    · simp [extendedGauge, hz, hh.zero, hg.zero]
    · have hp : 0 < r.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
      have hs := (div_lt_iff₀ (hg.positive _ hp)).mp (hbound ⟨hp, hr⟩)
      dsimp only [extendedGauge]
      rw [← ENNReal.ofReal_mul hc.le]
      exact ENNReal.ofReal_le_ofReal hs.le
  exact Measure.mkMetric_mono_smul ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hc) (hevent.filter_mono nhdsWithin_le_nhds)

/-- Finite measure for a larger gauge forces zero measure for any gauge with
vanishing ratio. This statement does not require the set to be measurable. -/
theorem hausdorffGauge_eq_zero_of_larger_finite
    {h g : ℝ → ℝ} (hh : IsGauge h) (hg : IsGauge g)
    (hratio : Tendsto (fun r => h r / g r) (𝓝[>] 0) (𝓝 0))
    {E : Set ℂ} (hfinite : hausdorffGauge g E < ∞) :
    hausdorffGauge h E = 0 := by
  have ht : Tendsto (fun c : ℝ => ENNReal.ofReal c * hausdorffGauge g E)
      (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hid)
      (Or.inr hfinite.ne)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hausdorffGauge_le_smul_of_ratio_tendsto_zero hh hg hratio hc E

/-- Positive measure for the smaller gauge prevents sigma-finiteness of the
larger Hausdorff measure restricted to that set. -/
theorem not_sigmaFinite_larger_of_positive
    {h g : ℝ → ℝ} (hh : IsGauge h) (hg : IsGauge g)
    (hratio : Tendsto (fun r => h r / g r) (𝓝[>] 0) (𝓝 0))
    {E : Set ℂ} (hpositive : 0 < hausdorffGauge h E) :
    ¬ SigmaFinite ((hausdorffGauge g).restrict E) := by
  intro hσ
  let : SigmaFinite ((hausdorffGauge g).restrict E) := hσ
  let A := spanningSets ((hausdorffGauge g).restrict E)
  have hzero (n : ℕ) : hausdorffGauge h (A n ∩ E) = 0 := by
    apply hausdorffGauge_eq_zero_of_larger_finite hh hg hratio
    have hf := measure_spanningSets_lt_top ((hausdorffGauge g).restrict E) n
    rwa [Measure.restrict_apply (measurableSet_spanningSets _ _)] at hf
  have hcover : (⋃ n, A n ∩ E) = E := by
    rw [← iUnion_inter]
    simp only [A, iUnion_spanningSets, univ_inter]
  have he : hausdorffGauge h E = 0 := by
    rw [← hcover]
    exact measure_iUnion_null hzero
  exact hpositive.ne' he

theorem hausdorffGauge_larger_eq_top_of_positive
    {h g : ℝ → ℝ} (hh : IsGauge h) (hg : IsGauge g)
    (hratio : Tendsto (fun r => h r / g r) (𝓝[>] 0) (𝓝 0))
    {E : Set ℂ} (hpositive : 0 < hausdorffGauge h E) :
    hausdorffGauge g E = ∞ := by
  by_contra htop
  exact hpositive.ne'
    (hausdorffGauge_eq_zero_of_larger_finite hh hg hratio (lt_top_iff_ne_top.mpr htop))

/-- Corollary `cor:larger-gauge`: once the explicit exact gauge has positive
measure on a set, the exponent-one gauge is not sigma-finite there. -/
theorem larger_logLog_gauge_not_sigmaFinite {κ : ℝ} (hκ : 0 < κ)
    {h g : ℝ → ℝ} (hh : IsGauge h) (hg : IsGauge g)
    (hf : HasSmallRadiusFormula h (hFormula κ))
    (gf : HasSmallRadiusFormula g (gFormula κ))
    {E : Set ℂ} (hpositive : 0 < hausdorffGauge h E) :
    ¬ SigmaFinite ((hausdorffGauge g).restrict E) :=
  not_sigmaFinite_larger_of_positive hh hg (gauge_ratio_tendsto_zero hκ hf gf) hpositive

end SLEExactGauge

end

end OAI
