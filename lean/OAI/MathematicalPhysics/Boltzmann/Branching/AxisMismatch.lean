import OAI.MathematicalPhysics.Boltzmann.Branching.MismatchSlices

namespace OAI

/-! # Uniform suppression of nonzero axial mismatch near the output axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.MismatchSlices

namespace BoltzmannNonuniqueness.AxisMismatch

def incoming (v : Velocity) (δ : ℝ) : Set Velocity :=
  {p | δ ≤ |axial (v - p)|}

def region (v : Velocity) (R δ : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (incoming v δ ×ˢ univ)

theorem measurableSet_incoming (v : Velocity) (δ : ℝ) : MeasurableSet (incoming v δ) :=
  measurableSet_le measurable_const ((measurable_axial.comp (measurable_const.sub measurable_id)).abs)

theorem measurableSet_region (v : Velocity) (R δ : ℝ) : MeasurableSet (region v R δ) :=
  (measurableSet_ballRegion v R).inter ((measurableSet_incoming v δ).prod .univ)

theorem region_eq_restricted (c : Measure Velocity) [SFinite c] (q : ℝ)
    (v : Velocity) (R δ : ℝ) :
    ChartKernel.measure c (weightRatio q v) v (region v R δ) =
      ChartKernel.measure (c.restrict (incoming v δ)) (weightRatio q v) v (ballRegion v R) := by
  rw [measure_restrict_incoming c _ _ (measurableSet_incoming v δ),
    Measure.restrict_apply (measurableSet_ballRegion v R)]
  rfl

theorem weight_region_bound {q d R δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 0 < R) (hδ : 0 < δ) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ChartKernel.measure (sheetLaw d ρ) (weightRatio q v) v (region v R δ) ≤
      (2 * ENNReal.ofReal (mismatchCoefficient q R δ / W q v)) *
        (1 + ENNReal.ofReal (expectationConstant q / ‖transverse v‖)) := by
  have := transverseLaw_isProbabilityMeasure hd
  have := sheetLaw_isProbabilityMeasure hd ρ
  have hreg : ∀ᵐ p ∂transverseLaw d, RegularTransverse (transverse v) p := by
    obtain rfl | hdpos := hd.eq_or_lt
    · simpa only [transverseLaw, ite_true] using ae_regularTransverse_atom hv
    · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using ae_regularTransverse_gaussian hv d
  have hK := mismatchCoefficient_nonneg hq₁ hq₂ hR.le hδ.le
  have hW := W_pos q v
  have hμ : IsProbabilityMeasure ((transverseLaw d).prod ρ) := inferInstance
  rw [region_eq_restricted _ q v R δ,
    ← region_eq_measure _ (measurable_weightRatio q v) v (measurableSet_ballRegion v R)]
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂(sheetLaw d ρ).restrict (incoming v δ)) ≤ _
  rw [← lintegral_indicator (measurableSet_incoming v δ), sheetLaw, lintegral_map_equiv]
  have hpoint : ∀ᵐ p : Transverse × ℝ ∂(transverseLaw d).prod ρ,
      (incoming v δ).indicator (fun p => ballChartFiber q v p R) (SheetMeasures.join p) ≤
        ENNReal.ofReal (mismatchCoefficient q R δ / W q v) *
          (1 + ENNReal.ofReal (‖transverse v - p.1‖⁻¹)) := by
    filter_upwards [ae_regularTransverse_prod hreg (ρ := ρ)] with p hp
    by_cases hm : SheetMeasures.join p ∈ incoming v δ
    · rw [indicator_of_mem hm]
      have hm' : δ ≤ |axial v - p.2| := by
        change δ ≤ |axial (v - SheetMeasures.join p)| at hm
        rw [axial_sub] at hm
        change δ ≤ |axial v - axial (PlaneChart.join p.1 p.2)| at hm
        simpa only [axial_join] using hm
      have hb := (ballChartFiber_le_slice hR.le q v p).trans
        (normalizedBallSlice_mismatch hq₁ hq₂ hR hδ (transverse v) p.1 (axial v) p.2 hp hm')
      apply hb.trans_eq
      have hcoef : 0 ≤ mismatchCoefficient q R δ / transverseWeight q (transverse v) :=
        div_nonneg hK (transverseWeight_pos q _).le
      rw [W_eq_transverseWeight, ENNReal.ofReal_mul hcoef,
        ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hm]
      exact bot_le
  have hi := lintegral_mono_ae hpoint
  have hmeas : Measurable (fun p : Transverse × ℝ => ENNReal.ofReal (‖transverse v - p.1‖⁻¹)) := by
    fun_prop
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
    lintegral_one, measure_univ, lintegral_prod _ hmeas.aemeasurable] at hi
  simp only [lintegral_const, measure_univ, mul_one] at hi
  calc
    _ ≤ 2 * (ENNReal.ofReal (mismatchCoefficient q R δ / W q v) *
        (1 + ∫⁻ p, ENNReal.ofReal (‖transverse v - p‖⁻¹) ∂transverseLaw d)) :=
      mul_le_mul' le_rfl hi
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl
        (RegularChart.transverseLaw_inverse_norm_bound hq₁ hq₂ hd hv)))

theorem normalized_region_bound {q d R L δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 < R) (hδ : 0 < δ) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (region v R δ) ≤
      ENNReal.ofReal tiltConstant * (ENNReal.ofReal (4 * L) *
        ((2 * ENNReal.ofReal (mismatchCoefficient q R δ / W q v)) *
          (1 + ENNReal.ofReal (expectationConstant q / ‖transverse v‖)))) := by
  have hnorm := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_region v R δ) (measurableSet_region v R δ) (Subset.refl _)
    (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at hnorm
  have hdom := measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ) (weightRatio q v) v
    (region v R δ)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at hdom
  exact hnorm.trans (mul_le_mul' le_rfl (hdom.trans (mul_le_mul' le_rfl
    (weight_region_bound hq₁ hq₂ (by positivity : 0 ≤ 2 * d) hR hδ hv (axialProbability ρ hρ)))))

def powerValue (q L R δ r : ℝ) : ℝ :=
  (tiltConstant * (4 * L) * (2 * mismatchCoefficient q R δ)) *
    (r ^ q + expectationConstant q * r ^ (q - 1))

theorem normalized_region_power_bound {q d R L δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 < R) (hδ : 0 < δ) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (region v R δ) ≤
      ENNReal.ofReal (powerValue q L R δ ‖transverse v‖) := by
  apply (normalized_region_bound hq₁ hq₂ hd hdmax hR hδ hv hρ).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  have hr : 0 < ‖transverse v‖ := norm_pos_iff.mpr hv
  have hL := hρ.nonneg
  have hK := mismatchCoefficient_nonneg hq₁ hq₂ hR.le hδ.le
  have he := expectationConstant_pos q
  have ht := tiltConstant_pos
  have hW := W_pos q v
  have hbase : 0 ≤ tiltConstant * (4 * L) * (2 * mismatchCoefficient q R δ) := by positivity
  have hvalue : 0 ≤ powerValue q L R δ ‖transverse v‖ := by unfold powerValue; positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add (by norm_num : (1 : ℝ≥0∞) ≠ ∞) ENNReal.ofReal_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (show 0 ≤ 4 * L by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ mismatchCoefficient q R δ / W q v by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ expectationConstant q / ‖transverse v‖ by positivity),
    ENNReal.toReal_ofReal hvalue]
  have hf := add_le_add (inverse_weight_le_power hr q)
    (mul_le_mul_of_nonneg_left (regular_fraction_le_power hr q) he.le)
  have hh := mul_le_mul_of_nonneg_left hf hbase
  convert hh using 1
  unfold W singularity
  simp only [div_eq_mul_inv]
  ring
  rfl

theorem power_tendsto_zero {q : ℝ} (hq : 1 < q) (L R δ : ℝ) :
    Tendsto (fun r => ENNReal.ofReal (powerValue q L R δ r)) (nhds 0) (nhds 0) := by
  have hqpos := Real.continuous_rpow_const (show 0 ≤ q by linarith)
  have hqm := Real.continuous_rpow_const (show 0 ≤ q - 1 by linarith)
  have hc : Continuous (powerValue q L R δ) := by unfold powerValue; fun_prop
  have hz : powerValue q L R δ 0 = 0 := by
    unfold powerValue
    rw [Real.zero_rpow (by linarith : q ≠ 0), Real.zero_rpow (by linarith : q - 1 ≠ 0)]
    ring
  have h := (ENNReal.continuous_ofReal.comp hc).tendsto 0
  simpa only [Function.comp_def, hz, ENNReal.ofReal_zero] using h

/-- The full axial-mismatch limit, uniform in the output axial velocity. -/
theorem uniform_axis_mismatch {q L δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
      (_ : 0 ≤ d) (_ : d ≤ 1 / 8) (_ : AxialMoment ρ L)
      (v : Velocity) (_ : transverse v ≠ 0) (_ : ‖transverse v‖ ≤ η),
      normalizedMeasure (sheetLaw d ρ) q v (incoming v δ ×ˢ univ) ≤ ENNReal.ofReal ε := by
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((SheetTightness.tendsto_tailBound q L).eventually (gt_mem_nhds he))
  have hi := (power_tendsto_zero hq₁ L (2 * ((N : ℝ) + 1)) δ).eventually (gt_mem_nhds he)
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp hi
  refine ⟨r / 2, by linarith, ?_⟩
  intro d ρ hprob hd hdmax hρ v hv hvsmall
  have hdist : dist ‖transverse v‖ 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    linarith
  have hsub : incoming v δ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ SheetTightness.tailRegion v N ∪
      region v (2 * ((N : ℝ) + 1)) δ := by
    intro y hy
    by_cases hh : 2 * ((N : ℝ) + 1) < radius v y
    · exact Or.inl hh
    · exact Or.inr ⟨(le_add_of_nonneg_left (norm_nonneg y.1)).trans (le_of_not_gt hh), hy⟩
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ SheetTightness.tailBound q L N +
        ENNReal.ofReal (powerValue q L (2 * ((N : ℝ) + 1)) δ ‖transverse v‖) :=
      add_le_add (SheetTightness.normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ N)
        (normalized_region_power_bound hq₁ hq₂ hd hdmax (by positivity) hδ hv hρ)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hN N le_rfl).le (hsmall hdist).le
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end BoltzmannNonuniqueness.AxisMismatch

end

end OAI
