import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain
import OAI.MathematicalPhysics.Boltzmann.Branching.RegularChart

namespace OAI

section

/-!
# Geometric exclusion of the axis for a nearly axial incoming sheet

Small transverse incoming velocity and small axial mismatch force the
collision plane away from the transverse origin. This is the geometric
part of the off-axis small-input estimate in Section 3.
-/

noncomputable section

open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.AxisGeometry

theorem normal_lower_bound {r : ℝ} {v p : Transverse}
    (hrv : r ≤ ‖v‖) (hp : ‖p‖ ≤ r / 4) :
    3 * r / 4 ≤ ‖v - p‖ := by
  have ht : ‖v‖ ≤ ‖v - p‖ + ‖p‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v - p) p
  linarith

theorem plane_offset_lower_bound {r : ℝ} (hr : 0 < r) {v p : Transverse}
    (hrv : r ≤ ‖v‖) (hp : ‖p‖ ≤ r / 4) :
    r / 2 * ‖v - p‖ ≤ inner ℝ (v - p) v := by
  have hv : 0 < ‖v‖ := hr.trans_le hrv
  have hi := (le_abs_self (inner ℝ p v)).trans (abs_real_inner_le_norm p v)
  have hn := norm_sub_le v p
  have h₁ : ‖p‖ * ‖v‖ ≤ r / 4 * ‖v‖ :=
    mul_le_mul_of_nonneg_right hp hv.le
  have h₂ : r * r ≤ r * ‖v‖ := mul_le_mul_of_nonneg_left hrv hr.le
  have h₃ : r * ‖p‖ ≤ r * (r / 4) := mul_le_mul_of_nonneg_left hp hr.le
  have h₄ : r / 2 * ‖v - p‖ ≤ r / 2 * (‖v‖ + ‖p‖) :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrv) (norm_nonneg v)]

theorem transverse_plane_exclusion {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {v p ξ : Velocity} (hrv : r ≤ ‖transverse v‖) (hp : ‖transverse p‖ ≤ r / 4)
    (ha : |axial (v - p)| ≤ r ^ 2 / (8 * R))
    (hz : |axial (ξ - v)| ≤ R)
    (hplane : inner ℝ (v - p) (ξ - v) = 0) :
    r / 3 ≤ ‖transverse ξ‖ := by
  have hn := normal_lower_bound hrv hp
  have hoff := plane_offset_lower_bound hr hrv hp
  have hi : inner ℝ (transverse v - transverse p) (transverse ξ) ≤
      ‖transverse v - transverse p‖ * ‖transverse ξ‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hzprod : |axial (v - p) * axial (ξ - v)| ≤ r ^ 2 / 8 := by
    rw [abs_mul]
    apply (mul_le_mul ha hz (abs_nonneg _) (by positivity)).trans_eq
    field_simp
  have he : inner ℝ (transverse v - transverse p) (transverse v) =
      inner ℝ (transverse v - transverse p) (transverse ξ) +
        axial (v - p) * axial (ξ - v) := by
    rw [inner_split, transverse_sub, transverse_sub, inner_sub_right] at hplane
    linarith
  have hx := le_of_abs_le hzprod
  rw [he] at hoff
  by_contra hbad
  have hbad' : ‖transverse ξ‖ < r / 3 := lt_of_not_ge hbad
  have hgap : 0 < ‖transverse v - transverse p‖ := by linarith
  have hs := mul_lt_mul_of_pos_left hbad' hgap
  have ht := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ r / 6)
  nlinarith

theorem chart_exclusion {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {v p : Velocity} (hrv : r ≤ ‖transverse v‖) (hp : ‖transverse p‖ ≤ r / 4)
    (ha : |axial (v - p)| ≤ r ^ 2 / (8 * R)) {z s : ℝ} (hz : |z| ≤ R) :
    r / 3 ≤ ‖transverse (chart v p z s)‖ := by
  have hn : normal v p ≠ 0 := by
    have h := normal_lower_bound hrv hp
    rw [normal, transverse_sub]
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) h)
  apply transverse_plane_exclusion hr hR hrv hp ha
  · simpa only [axial_sub, axial_chart, add_sub_cancel_left] using hz
  · exact chart_on_plane v p z s hn

end BoltzmannNonuniqueness.AxisGeometry

end

end

section

/-! # Suppression of transverse input away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.RegularChart

namespace BoltzmannNonuniqueness.AxisInput

def away (v : Velocity) (δ : ℝ) : Set Coordinates :=
  {y | δ ≤ ‖transverse (chart v y.1 y.2.1 y.2.2)‖}

def awayBall (v : Velocity) (R δ : ℝ) : Set Coordinates := ballRegion v R ∩ away v δ

theorem measurableSet_away (v : Velocity) (δ : ℝ) : MeasurableSet (away v δ) :=
  measurableSet_le measurable_const (measurable_transverse.comp (measurable_point v)).norm

theorem measurableSet_awayBall (v : Velocity) (R δ : ℝ) : MeasurableSet (awayBall v R δ) :=
  (measurableSet_ballRegion v R).inter (measurableSet_away v δ)

theorem weight_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (v ξ : Velocity)
    (hξ : δ ≤ ‖transverse ξ‖) :
    W q ξ / W q v ≤ (1 + δ ^ (-q)) / W q v := by
  apply div_le_div_of_nonneg_right _ (W_pos q v).le
  have h := Real.rpow_le_rpow_of_nonpos hδ hξ (neg_nonpos.mpr hq)
  change 1 + ‖transverse ξ‖ ^ (-q) ≤ 1 + δ ^ (-q)
  linarith

theorem weight_awayBall_le (c : Measure Velocity) {q δ : ℝ}
    (hq : 0 ≤ q) (hδ : 0 < δ) (v : Velocity) (R : ℝ) :
    ChartKernel.measure c (weightRatio q v) v (awayBall v R δ) ≤
      ENNReal.ofReal ((1 + δ ^ (-q)) / W q v) *
        ChartKernel.measure c (fun _ => 1) v (ballRegion v R) := by
  have h := restriction_comparison c (w := fun _ => 1) (h := weightRatio q v) (k := fun _ => 1)
    measurable_const measurable_const v (ENNReal.ofReal ((1 + δ ^ (-q)) / W q v))
    (measurableSet_awayBall v R δ) (measurableSet_ballRegion v R) ?_
  · have he : c.withDensity (fun _ => (1 : ℝ≥0∞)) = c := by
      ext s hs
      rw [withDensity_apply _ hs]
      simp
    rwa [he] at h
  intro y
  by_cases hy : y ∈ awayBall v R δ
  · rw [indicator_of_mem hy, indicator_of_mem hy.1]
    have hb := ENNReal.ofReal_le_ofReal (weight_bound hq hδ v _ hy.2)
    have hc := mul_le_mul_left hb (2 * ENNReal.ofReal (‖normal v y.1‖⁻¹))
    simpa only [density, weightRatio, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hc
  · rw [indicator_of_notMem hy]
    exact bot_le

theorem normalized_awayBall_bound {q d R L δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 ≤ R) (hδ : 0 < δ) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (awayBall v R δ) ≤
      ENNReal.ofReal tiltConstant *
        (ENNReal.ofReal (4 * L) *
          (ENNReal.ofReal ((1 + δ ^ (-q)) / W q v) *
            ((2 * ENNReal.ofReal (4 * R ^ 2)) *
              ENNReal.ofReal (TransverseAverage.expectationConstant q / ‖transverse v‖)))) := by
  have hnorm := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_awayBall v R δ) (measurableSet_awayBall v R δ) (Subset.refl _)
    (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at hnorm
  have hdom := measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ) (weightRatio q v) v
    (awayBall v R δ)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at hdom
  apply hnorm.trans
  apply mul_le_mul' le_rfl
  apply hdom.trans
  apply mul_le_mul' le_rfl
  apply (weight_awayBall_le _ (by linarith) hδ v R).trans
  apply mul_le_mul' le_rfl
  rw [← region_eq_measure _ measurable_const _ (measurableSet_ballRegion v R)]
  exact one_ball_sheet_bound hq₁ hq₂ (by positivity : 0 ≤ 2 * d) hR hv (axialProbability ρ hρ)

def powerConstant (q L R δ : ℝ) : ℝ :=
  tiltConstant * (4 * L) * (1 + δ ^ (-q)) * (8 * R ^ 2) *
    TransverseAverage.expectationConstant q

theorem powerConstant_nonneg (q : ℝ) {L : ℝ} (hL : 0 ≤ L) (R : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ powerConstant q L R δ := by
  have := tiltConstant_pos
  have := TransverseAverage.expectationConstant_pos q
  unfold powerConstant
  positivity

theorem normalized_awayBall_power_bound {q d R L δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 ≤ R) (hδ : 0 < δ) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (awayBall v R δ) ≤
      ENNReal.ofReal (powerConstant q L R δ * ‖transverse v‖ ^ (q - 1)) := by
  apply (normalized_awayBall_bound hq₁ hq₂ hd hdmax hR hδ hv hρ).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  have hr : 0 < ‖transverse v‖ := norm_pos_iff.mpr hv
  have hL := hρ.nonneg
  have hc := powerConstant_nonneg q hL R hδ.le
  have he := TransverseAverage.expectationConstant_pos q
  have ht := tiltConstant_pos
  have hw := W_pos q v
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (show 0 ≤ 4 * L by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ (1 + δ ^ (-q)) / W q v by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ 4 * R ^ 2 by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ TransverseAverage.expectationConstant q / ‖transverse v‖ by positivity),
    ENNReal.toReal_ofReal (mul_nonneg hc (Real.rpow_nonneg hr.le _))]
  have hb := mul_le_mul_of_nonneg_left (regular_fraction_le_power hr q) hc
  convert hb using 1
  unfold powerConstant W singularity
  simp only [div_eq_mul_inv]
  ring

theorem power_tendsto_zero {q : ℝ} (hq : 1 < q) (L R δ : ℝ) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (powerConstant q L R δ * r ^ (q - 1)))
      (nhds 0) (nhds 0) := by
  have hp := Real.continuous_rpow_const (show 0 ≤ q - 1 by linarith)
  have hc : Continuous (fun r : ℝ => powerConstant q L R δ * r ^ (q - 1)) := by fun_prop
  have h := (ENNReal.continuous_ofReal.comp hc).tendsto 0
  simpa only [Function.comp_def, Real.zero_rpow (by linarith : q - 1 ≠ 0),
    mul_zero, ENNReal.ofReal_zero] using h

/-- The first axis-input limit, with the output-speed restriction unnecessary. -/
theorem uniform_axis_input {q L δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
      (_ : 0 ≤ d) (_ : d ≤ 1 / 8) (_ : AxialMoment ρ L)
      (v : Velocity) (_ : transverse v ≠ 0) (_ : ‖transverse v‖ ≤ η),
      normalizedMeasure (sheetLaw d ρ) q v (away v δ) ≤ ENNReal.ofReal ε := by
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
  have hsub : away v δ ⊆ SheetTightness.tailRegion v N ∪
      awayBall v (2 * ((N : ℝ) + 1)) δ := by
    intro y hy
    by_cases hh : 2 * ((N : ℝ) + 1) < radius v y
    · exact Or.inl hh
    · exact Or.inr ⟨(le_add_of_nonneg_left (norm_nonneg y.1)).trans (le_of_not_gt hh), hy⟩
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ SheetTightness.tailBound q L N +
        ENNReal.ofReal (powerConstant q L (2 * ((N : ℝ) + 1)) δ * ‖transverse v‖ ^ (q - 1)) :=
      add_le_add (SheetTightness.normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ N)
        (normalized_awayBall_power_bound hq₁ hq₂ hd hdmax (by positivity) hδ hv hρ)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hN N le_rfl).le (hsmall hdist).le
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end BoltzmannNonuniqueness.AxisInput

end

end

end OAI
