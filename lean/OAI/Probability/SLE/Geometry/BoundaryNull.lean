import OAI.Probability.SLE.Gauge.GaugeCompletion

namespace OAI

/-! Real-boundary cleanup in the all-time upper Hausdorff estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The log-log correction is smaller than every power lost from dimension. -/
theorem hFormula_div_rpow_tendsto_zero {κ s : ℝ}
    (hκ : 0 < κ) (hs : s < dimension κ) :
    Tendsto (fun r => hFormula κ r / r ^ s) (𝓝[>] 0) (𝓝 0) := by
  have hq : codimension κ / 2 ≤ 1 := by
    dsimp [codimension, dimension]
    linarith
  have ht := (GaugeCompletion.tailProfile_tendsto_zero (sub_pos.mpr hs) hq).comp
    GaugeCompletion.log_inv_tendsto_atTop
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change GaugeCompletion.tailProfile (dimension κ - s) (codimension κ / 2)
    (Real.log (1 / r)) = _
  rw [GaugeCompletion.tailProfile_log_inv hr]
  unfold hFormula
  rw [Real.rpow_sub hr]
  ring_nf

/-- An eventual power bound compares the diameter-defined gauge measure with
ordinary Hausdorff measure. -/
theorem hausdorffGauge_le_hausdorffMeasure_of_power_bound
    {h : ℝ → ℝ} (hh : IsGauge h) {s : ℝ} (hs : 0 ≤ s)
    (hb : ∀ᶠ r in 𝓝[>] (0 : ℝ), h r ≤ r ^ s) :
    hausdorffGauge h ≤ (Measure.hausdorffMeasure s : Measure ℂ) := by
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  have ht : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ)) := by
    simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top
  apply Measure.mkMetric_mono
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with r hr
  change ENNReal.ofReal (h r.toReal) ≤ r ^ s
  by_cases hz : r.toReal = 0
  · simp only [hz, hh.zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hp : 0 < r.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
    calc
      ENNReal.ofReal (h r.toReal) ≤ ENNReal.ofReal (r.toReal ^ s) :=
        ENNReal.ofReal_le_ofReal (hbound ⟨hp, hr⟩)
      _ = (ENNReal.ofReal r.toReal) ^ s :=
        (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs).symm
      _ ≤ r ^ s := ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hs

/-- Every continuous completion of the explicit gauge gives zero measure to
the entire real axis, hence also to its trace points in any bounded disk. -/
theorem explicit_gauge_real_axis_null {κ : ℝ} (hκ : 0 < κ)
    {h : ℝ → ℝ} (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    hausdorffGauge h (range ((↑) : ℝ → ℂ)) = 0 := by
  let s : ℝ := (1 + dimension κ) / 2
  have hd : 1 < dimension κ := by dsimp [dimension]; linarith
  have hs1 : 1 < s := by dsimp [s]; linarith
  have hsd : s < dimension κ := by dsimp [s]; linarith
  have ht : Tendsto (fun r => h r / r ^ s) (𝓝[>] 0) (𝓝 0) := by
    apply (hFormula_div_rpow_tendsto_zero hκ hsd).congr'
    filter_upwards [hf] with r hr
    rw [hr]
  have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ), h r ≤ r ^ s := by
    filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds zero_lt_one)] with r hr hb
    exact ((div_lt_one (Real.rpow_pos_of_pos hr s)).mp hb).le
  have hcomp := hausdorffGauge_le_hausdorffMeasure_of_power_bound hh
    (zero_lt_one.trans hs1).le hb
  apply le_antisymm _ bot_le
  apply (hcomp _).trans
  have he := Complex.isometry_ofReal.hausdorffMeasure_image
    (Or.inl (zero_lt_one.trans hs1).le) (univ : Set ℝ)
  rw [image_univ] at he
  rw [he, Real.hausdorffMeasure_of_finrank_lt (by simpa using hs1)]
  simp

end SLEExactGauge

end

end OAI
