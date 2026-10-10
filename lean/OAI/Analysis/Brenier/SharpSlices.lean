import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem358.SharpSlice

def centralInterval (r : ℝ) : Set ℝ := {s | |s| < r}

lemma centralInterval_eq_Ioo (r : ℝ) :
    centralInterval r = Ioo (-r) r := by
  ext s
  change |s| < r ↔ -r < s ∧ s < r
  exact abs_lt

lemma centralInterval_mono {r q : ℝ} (h : r ≤ q) :
    centralInterval r ⊆ centralInterval q := by
  intro s hs
  exact lt_of_lt_of_le hs h

lemma measurableSet_centralInterval (r : ℝ) : MeasurableSet (centralInterval r) := by
  rw [centralInterval_eq_Ioo]
  exact measurableSet_Ioo

lemma volume_centralInterval (r : ℝ) :
    volume (centralInterval r) = ENNReal.ofReal (2 * r) := by
  rw [centralInterval_eq_Ioo, Real.volume_Ioo]
  congr 1
  ring

lemma volume_centralInterval_symmDiff {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    volume (symmDiff (centralInterval r) (centralInterval q)) =
      ENNReal.ofReal (2 * |q - r|) := by
  rcases le_total r q with h | h
  · rw [symmDiff_of_le (centralInterval_mono h),
      measure_sdiff (centralInterval_mono h)
        (measurableSet_centralInterval r).nullMeasurableSet
        (by rw [volume_centralInterval]; exact ENNReal.ofReal_ne_top),
      volume_centralInterval, volume_centralInterval,
      ← ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) hr),
      abs_of_nonneg (sub_nonneg.mpr h)]
    congr 1
    ring
  · rw [symmDiff_of_ge (centralInterval_mono h),
      measure_sdiff (centralInterval_mono h)
        (measurableSet_centralInterval q).nullMeasurableSet
        (by rw [volume_centralInterval]; exact ENNReal.ofReal_ne_top),
      volume_centralInterval, volume_centralInterval,
      ← ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) hq),
      abs_of_nonpos (sub_nonpos.mpr h)]
    congr 1
    ring

/-- A central interval clipped to the source coordinate range. -/
def centralSlice (r : ℝ) : Set ℝ := Icc (-1) 1 ∩ centralInterval r

lemma centralSlice_eq {r : ℝ} (hr : r ≤ 1) :
    centralSlice r = centralInterval r := by
  apply inter_eq_right.mpr
  intro s hs
  change |s| < r at hs
  obtain ⟨hl, hu⟩ := abs_lt.mp hs
  exact ⟨by linarith, by linarith⟩

lemma volume_centralSlice {r : ℝ} (hr : r ≤ 1) :
    volume (centralSlice r) = ENNReal.ofReal (2 * r) := by
  rw [centralSlice_eq hr, volume_centralInterval]

lemma tiltedRadius_bounds {a b t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) (ht : |t| ≤ 1) :
    0 ≤ a + b * t ∧ a + b * t ≤ 1 := by
  obtain ⟨htl, htu⟩ := abs_le.mp ht
  have hbl := mul_le_mul_of_nonneg_left htl hb
  have hbu := mul_le_mul_of_nonneg_left htu hb
  constructor <;> nlinarith

lemma volume_tilted_centralSlice {a b t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) (ht : |t| ≤ 1) :
    volume (centralSlice (a + b * t)) = ENNReal.ofReal (2 * (a + b * t)) := by
  exact volume_centralSlice (tiltedRadius_bounds hb hba hab ht).2

lemma volume_centralSlice_symmDiff {a b t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) (ht : |t| ≤ 1) :
    volume (symmDiff (centralSlice a) (centralSlice (a + b * t))) =
      ENNReal.ofReal (2 * b * |t|) := by
  have ha : 0 ≤ a := le_trans hb hba
  obtain ⟨hr0, hr1⟩ := tiltedRadius_bounds hb hba hab ht
  rw [centralSlice_eq (by linarith : a ≤ 1), centralSlice_eq hr1,
    volume_centralInterval_symmDiff ha hr0]
  congr 1
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hb]
  ring

/-- The negative outer cell of the sharpness map, with all ties assigned centrally. -/
def leftOuterSlice (r : ℝ) : Set ℝ := Icc (-1) 1 ∩ Iio (-r)

/-- The positive outer cell of the sharpness map, with all ties assigned centrally. -/
def rightOuterSlice (r : ℝ) : Set ℝ := Icc (-1) 1 ∩ Ioi r

lemma leftOuterSlice_eq_Ico {r : ℝ} (hr : 0 ≤ r) :
    leftOuterSlice r = Ico (-1) (-r) := by
  ext s
  change ((-1 ≤ s ∧ s ≤ 1) ∧ s < -r) ↔ (-1 ≤ s ∧ s < -r)
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩

lemma rightOuterSlice_eq_Ioc {r : ℝ} (hr : 0 ≤ r) :
    rightOuterSlice r = Ioc r 1 := by
  ext s
  change ((-1 ≤ s ∧ s ≤ 1) ∧ r < s) ↔ (r < s ∧ s ≤ 1)
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨by linarith [h.1], h.2⟩, h.1⟩

lemma volume_leftOuterSlice {r : ℝ} (hr : 0 ≤ r) :
    volume (leftOuterSlice r) = ENNReal.ofReal (1 - r) := by
  rw [leftOuterSlice_eq_Ico hr, Real.volume_Ico]
  congr 1
  ring

lemma volume_rightOuterSlice {r : ℝ} (hr : 0 ≤ r) :
    volume (rightOuterSlice r) = ENNReal.ofReal (1 - r) := by
  rw [rightOuterSlice_eq_Ioc hr, Real.volume_Ioc]

lemma leftOuterSlice_eq_mapRegion {r : ℝ} (hr : 0 ≤ r) :
    leftOuterSlice r = {s | s ∈ Icc (-1) 1 ∧ ¬ |s| ≤ r ∧ s < 0} := by
  ext s
  change (s ∈ Icc (-1) 1 ∧ s < -r) ↔
    (s ∈ Icc (-1) 1 ∧ ¬ |s| ≤ r ∧ s < 0)
  constructor
  · rintro ⟨hs, hsr⟩
    have hs0 : s < 0 := by linarith
    refine ⟨hs, ?_, hs0⟩
    rw [abs_of_neg hs0]
    linarith
  · rintro ⟨hs, hsr, hs0⟩
    refine ⟨hs, ?_⟩
    rw [abs_of_neg hs0] at hsr
    linarith

lemma rightOuterSlice_eq_mapRegion {r : ℝ} (hr : 0 ≤ r) :
    rightOuterSlice r = {s | s ∈ Icc (-1) 1 ∧ ¬ |s| ≤ r ∧ ¬ s < 0} := by
  ext s
  change (s ∈ Icc (-1) 1 ∧ r < s) ↔
    (s ∈ Icc (-1) 1 ∧ ¬ |s| ≤ r ∧ ¬ s < 0)
  constructor
  · rintro ⟨hs, hrs⟩
    have hs0 : 0 ≤ s := by linarith
    refine ⟨hs, ?_, not_lt.mpr hs0⟩
    rw [abs_of_nonneg hs0]
    linarith
  · rintro ⟨hs, hsr, hs0⟩
    refine ⟨hs, ?_⟩
    rw [abs_of_nonneg (not_lt.mp hs0)] at hsr
    linarith

lemma volume_tilted_leftOuterSlice {a b t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) (ht : |t| ≤ 1) :
    volume (leftOuterSlice (a + b * t)) = ENNReal.ofReal (1 - a - b * t) := by
  rw [volume_leftOuterSlice (tiltedRadius_bounds hb hba hab ht).1]
  congr 1
  ring

lemma volume_tilted_rightOuterSlice {a b t : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) (ht : |t| ≤ 1) :
    volume (rightOuterSlice (a + b * t)) = ENNReal.ofReal (1 - a - b * t) := by
  rw [volume_rightOuterSlice (tiltedRadius_bounds hb hba hab ht).1]
  congr 1
  ring

end Problem358.SharpSlice

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace Problem358

/-- The one-dimensional central cell in the sharpness construction. -/
def centralInterval (r : ℝ) : Set ℝ := {s | |s| < r}

lemma centralInterval_eq_Ioo (r : ℝ) : centralInterval r = Ioo (-r) r := by
  ext s
  change |s| < r ↔ -r < s ∧ s < r
  exact abs_lt

lemma measurableSet_centralInterval (r : ℝ) : MeasurableSet (centralInterval r) := by
  rw [centralInterval_eq_Ioo]
  exact measurableSet_Ioo

lemma centralInterval_mono {a r : ℝ} (har : a ≤ r) :
    centralInterval a ⊆ centralInterval r := by
  intro s hs
  exact lt_of_lt_of_le hs har

lemma volume_centralInterval (r : ℝ) :
    volume (centralInterval r) = ENNReal.ofReal (2 * r) := by
  rw [centralInterval_eq_Ioo, Real.volume_Ioo]
  congr 1
  ring

lemma centralInterval_subset_unit {r : ℝ} (hr : r ≤ 1) :
    centralInterval r ⊆ Icc (-1 : ℝ) 1 := by
  intro s hs
  have h : |s| ≤ 1 := (le_of_lt hs).trans hr
  exact abs_le.mp h

lemma restricted_volume_centralInterval {r : ℝ} (hr : r ≤ 1) :
    (volume.restrict (Icc (-1 : ℝ) 1)) (centralInterval r) =
      ENNReal.ofReal (2 * r) := by
  rw [Measure.restrict_apply (measurableSet_centralInterval r),
    inter_eq_left.mpr (centralInterval_subset_unit hr), volume_centralInterval]

lemma volume_centralInterval_symmDiff {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    volume (centralInterval a ∆ centralInterval r) =
      ENNReal.ofReal (2 * |r - a|) := by
  rcases le_total a r with har | hra
  · rw [symmDiff_of_le (centralInterval_mono har)]
    rw [measure_sdiff (centralInterval_mono har)
      (measurableSet_centralInterval a).nullMeasurableSet
      (by rw [volume_centralInterval]; exact ENNReal.ofReal_ne_top)]
    rw [volume_centralInterval, volume_centralInterval,
      ← ENNReal.ofReal_sub _ (by positivity), abs_of_nonneg (sub_nonneg.mpr har)]
    congr 1
    ring
  · rw [symmDiff_of_ge (centralInterval_mono hra)]
    rw [measure_sdiff (centralInterval_mono hra)
      (measurableSet_centralInterval r).nullMeasurableSet
      (by rw [volume_centralInterval]; exact ENNReal.ofReal_ne_top)]
    rw [volume_centralInterval, volume_centralInterval,
      ← ENNReal.ofReal_sub _ (by positivity), abs_of_nonpos (sub_nonpos.mpr hra)]
    congr 1
    ring

lemma restricted_volume_centralInterval_symmDiff {a r : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (volume.restrict (Icc (-1 : ℝ) 1))
      (centralInterval a ∆ centralInterval r) =
        ENNReal.ofReal (2 * |r - a|) := by
  rw [Measure.restrict_apply
    ((measurableSet_centralInterval a).symmDiff (measurableSet_centralInterval r))]
  rw [inter_eq_left.mpr, volume_centralInterval_symmDiff ha hr]
  exact symmDiff_subset_union.trans
    (union_subset (centralInterval_subset_unit ha1) (centralInterval_subset_unit hr1))

/-- The uniform probability law on the interval `[-1,1]`. -/
def sharpSliceLaw : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict (Icc (-1 : ℝ) 1)

instance sharpSliceLaw_isProbabilityMeasure : IsProbabilityMeasure sharpSliceLaw := by
  constructor
  change ENNReal.ofReal (1 / 2 : ℝ) *
    (volume.restrict (Icc (-1 : ℝ) 1)) univ = 1
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma sharpSliceLaw_centralInterval {r : ℝ} (hr : r ≤ 1) :
    sharpSliceLaw (centralInterval r) = ENNReal.ofReal r := by
  rw [sharpSliceLaw, Measure.smul_apply, smul_eq_mul,
    restricted_volume_centralInterval hr, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

lemma sharpSliceLaw_centralInterval_symmDiff {a r : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    sharpSliceLaw (centralInterval a ∆ centralInterval r) =
      ENNReal.ofReal |r - a| := by
  rw [sharpSliceLaw, Measure.smul_apply, smul_eq_mul,
    restricted_volume_centralInterval_symmDiff ha ha1 hr hr1,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

lemma sharp_tilted_radius_bounds {a t : ℝ}
    (ha : 0 < a) (ha1 : a < 1 / 2) (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ a + (a / 2) * t ∧ a + (a / 2) * t ≤ 1 := by
  constructor <;> nlinarith [ht.1, ht.2]

lemma sharpSliceLaw_tiltedCentral {a t : ℝ}
    (ha : 0 < a) (ha1 : a < 1 / 2) (ht : t ∈ Icc (-1 : ℝ) 1) :
    sharpSliceLaw (centralInterval (a + (a / 2) * t)) =
      ENNReal.ofReal (a + (a / 2) * t) :=
  sharpSliceLaw_centralInterval (sharp_tilted_radius_bounds ha ha1 ht).2

lemma sharpSliceLaw_tiltedSymmDiff {a t : ℝ}
    (ha : 0 < a) (ha1 : a < 1 / 2) (ht : t ∈ Icc (-1 : ℝ) 1) :
    sharpSliceLaw (centralInterval a ∆ centralInterval (a + (a / 2) * t)) =
      ENNReal.ofReal ((a / 2) * |t|) := by
  rw [sharpSliceLaw_centralInterval_symmDiff ha.le (by linarith)
    (sharp_tilted_radius_bounds ha ha1 ht).1 (sharp_tilted_radius_bounds ha ha1 ht).2]
  congr 1
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a / 2)]

lemma integral_sharpSliceLaw (f : ℝ → ℝ) :
    (∫ t, f t ∂sharpSliceLaw) = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, f t := by
  rw [sharpSliceLaw, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num),
    smul_eq_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

lemma integral_id_sharpSliceLaw : (∫ t, t ∂sharpSliceLaw) = 0 := by
  rw [integral_sharpSliceLaw, integral_id]
  norm_num

lemma integral_affine_sharpSliceLaw (a b : ℝ) :
    (∫ t, a + b * t ∂sharpSliceLaw) = a := by
  have hconst : IntervalIntegrable (fun _ : ℝ => a) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun t : ℝ => b * t) volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_sharpSliceLaw, intervalIntegral.integral_add hconst hlin,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

lemma intervalIntegral_abs_unitInterval : (∫ t in (-1 : ℝ)..1, |t|) = 1 := by
  have hn : (∫ t in (-1 : ℝ)..0, |t|) = ∫ t in (-1 : ℝ)..0, -t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    exact abs_of_nonpos ht.2
  have hp : (∫ t in (0 : ℝ)..1, |t|) = ∫ t in (0 : ℝ)..1, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact abs_of_nonneg ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-1) 0) (continuous_abs.intervalIntegrable 0 1),
    hn, hp, intervalIntegral.integral_neg, integral_id, integral_id]
  norm_num

lemma integral_abs_sharpSliceLaw : (∫ t, |t| ∂sharpSliceLaw) = 1 / 2 := by
  rw [integral_sharpSliceLaw, intervalIntegral_abs_unitInterval]
  ring

lemma integral_mul_abs_sharpSliceLaw (b : ℝ) :
    (∫ t, b * |t| ∂sharpSliceLaw) = b / 2 := by
  rw [integral_const_mul, integral_abs_sharpSliceLaw]
  ring

/-- Closed central cells have the same slice law as open central cells. -/
def closedCentralInterval (r : ℝ) : Set ℝ := {s | |s| ≤ r}

lemma closedCentralInterval_eq_Icc (r : ℝ) : closedCentralInterval r = Icc (-r) r := by
  ext s
  change |s| ≤ r ↔ -r ≤ s ∧ s ≤ r
  exact abs_le

lemma centralInterval_ae_eq_closed (r : ℝ) :
    centralInterval r =ᵐ[sharpSliceLaw] closedCentralInterval r := by
  rw [centralInterval_eq_Ioo, closedCentralInterval_eq_Icc]
  exact Measure.ae_smul_measure (ae_restrict_of_ae (Ioo_ae_eq_Icc (μ := volume))) _

lemma sharpSliceLaw_closedCentralInterval {r : ℝ} (hr : r ≤ 1) :
    sharpSliceLaw (closedCentralInterval r) = ENNReal.ofReal r := by
  rw [← measure_congr (centralInterval_ae_eq_closed r)]
  exact sharpSliceLaw_centralInterval hr

lemma sharpSliceLaw_closedCentralInterval_symmDiff {a r : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    sharpSliceLaw (closedCentralInterval a ∆ closedCentralInterval r) =
      ENNReal.ofReal |r - a| := by
  rw [← measure_congr ((centralInterval_ae_eq_closed a).symmDiff
    (centralInterval_ae_eq_closed r))]
  exact sharpSliceLaw_centralInterval_symmDiff ha ha1 hr hr1

lemma ae_mem_sharpSliceLaw : ∀ᵐ t ∂sharpSliceLaw, t ∈ Icc (-1 : ℝ) 1 :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

lemma integrable_sharpSliceLaw_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f sharpSliceLaw :=
  hf.continuousOn.integrableOn_Icc.smul_measure ENNReal.ofReal_ne_top

lemma lintegral_tiltedRadius_sharpSliceLaw {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1 / 2) :
    (∫⁻ t, ENNReal.ofReal (a + (a / 2) * t) ∂sharpSliceLaw) =
      ENNReal.ofReal a := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_sharpSliceLaw_of_continuous (f := fun t : ℝ => a + (a / 2) * t)
      (continuous_const.add (continuous_const.mul continuous_id)))]
  · rw [integral_affine_sharpSliceLaw]
  · filter_upwards [ae_mem_sharpSliceLaw] with t ht
    exact (sharp_tilted_radius_bounds ha ha1 ht).1

lemma lintegral_mul_abs_sharpSliceLaw {b : ℝ} (hb : 0 ≤ b) :
    (∫⁻ t, ENNReal.ofReal (b * |t|) ∂sharpSliceLaw) = ENNReal.ofReal (b / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_sharpSliceLaw_of_continuous (f := fun t : ℝ => b * |t|)
      (continuous_const.mul continuous_abs))]
  · rw [integral_mul_abs_sharpSliceLaw]
  · exact Filter.Eventually.of_forall fun t => mul_nonneg hb (abs_nonneg t)

lemma lintegral_affine_sharpSliceLaw {a b : ℝ} (hab : |b| ≤ a) :
    (∫⁻ t, ENNReal.ofReal (a + b * t) ∂sharpSliceLaw) = ENNReal.ofReal a := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_sharpSliceLaw_of_continuous (f := fun t : ℝ => a + b * t)
      (continuous_const.add (continuous_const.mul continuous_id)))]
  · rw [integral_affine_sharpSliceLaw]
  · filter_upwards [ae_mem_sharpSliceLaw] with t ht
    have ht' : |t| ≤ 1 := abs_le.mpr ht
    have hbt : |b * t| ≤ a := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ht' (abs_nonneg b)).trans (by simpa using hab)
    have := neg_abs_le (b * t)
    change 0 ≤ a + b * t
    linarith

lemma lintegral_centralSlices {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2) :
    (∫⁻ t, sharpSliceLaw (centralInterval (a + (a / 2) * t)) ∂sharpSliceLaw) =
      ENNReal.ofReal a := by
  calc
    _ = ∫⁻ t, ENNReal.ofReal (a + (a / 2) * t) ∂sharpSliceLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_sharpSliceLaw] with t ht
      exact sharpSliceLaw_tiltedCentral ha ha1 ht
    _ = _ := lintegral_tiltedRadius_sharpSliceLaw ha ha1

lemma lintegral_symmDiffSlices {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2) :
    (∫⁻ t, sharpSliceLaw
      (centralInterval a ∆ centralInterval (a + (a / 2) * t)) ∂sharpSliceLaw) =
        ENNReal.ofReal (a / 4) := by
  calc
    _ = ∫⁻ t, ENNReal.ofReal ((a / 2) * |t|) ∂sharpSliceLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_sharpSliceLaw] with t ht
      exact sharpSliceLaw_tiltedSymmDiff ha ha1 ht
    _ = ENNReal.ofReal ((a / 2) / 2) := lintegral_mul_abs_sharpSliceLaw (by positivity)
    _ = _ := by congr 1; ring

lemma lintegral_closedCentralSlices {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2) :
    (∫⁻ t, sharpSliceLaw (closedCentralInterval (a + (a / 2) * t)) ∂sharpSliceLaw) =
      ENNReal.ofReal a := by
  rw [← lintegral_centralSlices ha ha1]
  apply lintegral_congr
  intro t
  exact (measure_congr (centralInterval_ae_eq_closed (a + (a / 2) * t))).symm

lemma lintegral_closedSymmDiffSlices {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2) :
    (∫⁻ t, sharpSliceLaw
      (closedCentralInterval a ∆ closedCentralInterval (a + (a / 2) * t))
        ∂sharpSliceLaw) = ENNReal.ofReal (a / 4) := by
  rw [← lintegral_symmDiffSlices ha ha1]
  apply lintegral_congr
  intro t
  exact (measure_congr ((centralInterval_ae_eq_closed a).symmDiff
    (centralInterval_ae_eq_closed (a + (a / 2) * t)))).symm

end Problem358

end

end OAI
