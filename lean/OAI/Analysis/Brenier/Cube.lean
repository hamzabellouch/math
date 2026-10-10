import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section
namespace Problem358

theorem cube_eq_coord_box (d : ℕ) :
    cube d = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
  rfl

theorem isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  rw [cube_eq_coord_box]
  exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr
    (isCompact_pi_infinite fun _ => isCompact_Icc)

theorem convex_cube (d : ℕ) : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab i
  change |a * x i + b * y i| ≤ 1
  have hxi := (abs_le.mp (hx i))
  have hyi := (abs_le.mp (hy i))
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxi.1),
      mul_nonneg hb (sub_nonneg.mpr hyi.1)]
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxi.2),
      mul_nonneg hb (sub_nonneg.mpr hyi.2)]

theorem zero_mem_cube (d : ℕ) : (0 : E d) ∈ cube d := by
  intro i
  simp

theorem cube_nonempty (d : ℕ) : (cube d).Nonempty := ⟨0, zero_mem_cube d⟩

theorem ball_zero_subset_cube (d : ℕ) : Metric.ball (0 : E d) 1 ⊆ cube d := by
  intro x hx i
  have hn : ‖x‖ < 1 := by simpa using hx
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact hi.trans hn.le

theorem zero_mem_interior_cube (d : ℕ) : (0 : E d) ∈ interior (cube d) := by
  apply mem_interior_iff_mem_nhds.mpr
  exact Metric.mem_nhds_iff.mpr ⟨1, by norm_num, ball_zero_subset_cube d⟩

theorem interior_cube_nonempty (d : ℕ) : (interior (cube d)).Nonempty :=
  ⟨0, zero_mem_interior_cube d⟩
end Problem358

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

private theorem cube_eq_preimage_pi (d : ℕ) :
    cube d = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      (Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp [cube, abs_le, Pi.le_def, forall_and]

/-- The Euclidean cube has its usual Lebesgue volume. -/
theorem volume_cube (d : ℕ) : volume (cube d) = (2 : ℝ≥0∞) ^ d := by
  rw [cube_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet,
    volume_pi_pi]
  norm_num [Real.volume_Icc]

/-- The uniform probability law on one coordinate of the cube. -/
def intervalUniform : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance intervalUniform_isProbabilityMeasure : IsProbabilityMeasure intervalUniform where
  measure_univ := by
    norm_num [intervalUniform, Real.volume_Icc]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The two-coordinate law is one quarter of planar area restricted to the square. -/
theorem intervalUniform_prod :
    intervalUniform.prod intervalUniform =
      (4 : ℝ≥0∞)⁻¹ • volume.restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := by
  simp only [intervalUniform, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict, ← Measure.volume_eq_prod]
  congr 1
  have h : (4 : ℝ≥0∞) = 2 ^ 2 := by norm_num
  rw [h, ENNReal.inv_pow, pow_two]

/-- Restricting Euclidean volume to the cube becomes the product of interval restrictions. -/
theorem map_ofLp_volume_restrict_cube (d : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin d → ℝ)) (volume.restrict (cube d)) =
      Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (-1 : ℝ) 1)) := by
  rw [cube_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) |>.map_eq,
    volume_pi, Measure.restrict_pi_pi]

/-- The normalized cube law is the product of normalized interval laws. -/
theorem map_ofLp_uniformMeasure_cube (d : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin d → ℝ)) (uniformMeasure (cube d)) =
      Measure.pi (fun _ : Fin d => intervalUniform) := by
  rw [uniformMeasure,
    Measure.map_smul _ (PiLp.volume_preserving_ofLp (Fin d)).measurable.aemeasurable,
    volume_cube, map_ofLp_volume_restrict_cube]
  apply (Measure.pi_eq fun s hs => ?_).symm
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, intervalUniform]
  rw [Finset.prod_mul_distrib]
  simp [ENNReal.inv_pow]

/-- Coordinate representation preserves the normalized cube law. -/
theorem measurePreserving_ofLp_uniformMeasure_cube (d : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin d → ℝ)) (uniformMeasure (cube d))
      (Measure.pi (fun _ : Fin d => intervalUniform)) :=
  ⟨(PiLp.volume_preserving_ofLp (Fin d)).measurable, map_ofLp_uniformMeasure_cube d⟩

/-- Every coordinate of the uniform cube is uniform on `[-1,1]`. -/
theorem measurePreserving_coord_uniformMeasure_cube {d : ℕ} (i : Fin d) :
    MeasurePreserving (fun x : E d => x i) (uniformMeasure (cube d)) intervalUniform :=
  (measurePreserving_eval (fun _ : Fin d => intervalUniform) i).comp
    (measurePreserving_ofLp_uniformMeasure_cube d)

/-- Two distinct coordinates of the uniform cube have the product interval law. -/
theorem measurePreserving_coordPair_uniformMeasure_cube {d : ℕ} (i j : Fin d)
    (hij : i ≠ j) :
    MeasurePreserving (fun x : E d => (x i, x j)) (uniformMeasure (cube d))
      (intervalUniform.prod intervalUniform) := by
  have hind : ProbabilityTheory.iIndepFun
      (fun i : Fin d => fun x : Fin d → ℝ => x i)
      (Measure.pi (fun _ : Fin d => intervalUniform)) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hp : MeasurePreserving (fun x : Fin d → ℝ => (x i, x j))
      (Measure.pi (fun _ : Fin d => intervalUniform))
      (intervalUniform.prod intervalUniform) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    rw [(hind.indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
      (measurePreserving_eval (fun _ : Fin d => intervalUniform) i).map_eq,
      (measurePreserving_eval (fun _ : Fin d => intervalUniform) j).map_eq]
  exact hp.comp (measurePreserving_ofLp_uniformMeasure_cube d)

/-- Integration of a function of two coordinates reduces to a two-dimensional product law. -/
theorem integral_coordPair_uniformMeasure_cube {d : ℕ} (i j : Fin d)
    (hij : i ≠ j) (f : ℝ × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (intervalUniform.prod intervalUniform)) :
    (∫ x, f (x i, x j) ∂uniformMeasure (cube d)) =
      ∫ p, f p ∂intervalUniform.prod intervalUniform := by
  have hp := measurePreserving_coordPair_uniformMeasure_cube i j hij
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

/-- The analogous nonnegative integral identity needs only measurability. -/
theorem lintegral_coordPair_uniformMeasure_cube {d : ℕ} (i j : Fin d)
    (hij : i ≠ j) (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (x i, x j) ∂uniformMeasure (cube d)) =
      ∫⁻ p, f p ∂intervalUniform.prod intervalUniform :=
  (measurePreserving_coordPair_uniformMeasure_cube i j hij).lintegral_comp hf

/-- A planar event depending on two distinct coordinates has one quarter its square area. -/
theorem uniformMeasure_cube_coordPair_preimage {d : ℕ} (i j : Fin d)
    (hij : i ≠ j) (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    uniformMeasure (cube d) ((fun x : E d => (x i, x j)) ⁻¹' s) =
      (4 : ℝ≥0∞)⁻¹ * volume
        (s ∩ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) := by
  rw [(measurePreserving_coordPair_uniformMeasure_cube i j hij).measure_preimage
    hs.nullMeasurableSet, intervalUniform_prod, Measure.smul_apply,
    Measure.restrict_apply hs, smul_eq_mul]

end Problem358

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358

/-- A central strip in the square, written in slice coordinates. -/
def planarStrip (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-1 : ℝ) 1 ∧ |p.1| ≤ a + b * p.2}

lemma measurableSet_planarStrip (a b : ℝ) : MeasurableSet (planarStrip a b) := by
  unfold planarStrip
  measurability

lemma volume_planarStrip_eq_lintegral (a b : ℝ) :
    volume (planarStrip a b) =
      ∫⁻ y in Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * (a + b * y)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_planarStrip a b)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarStrip a b =
        Icc (-(a + b * y)) (a + b * y) := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ |x| ≤ a + b * y) ↔ _
      simp only [hy, true_and, mem_Icc, abs_le]
    rw [hs, Real.volume_Icc, indicator_of_mem hy]
    congr 1
    ring
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarStrip a b = ∅ := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ |x| ≤ a + b * y) ↔ False
      simp only [hy, false_and]
    rw [hs, measure_empty, indicator_of_notMem hy]

lemma integral_strip_width (a b : ℝ) :
    (∫ y in Icc (-1 : ℝ) 1, 2 * (a + b * y)) = 4 * a := by
  have hi1 : IntervalIntegrable (fun _ : ℝ => a) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun y : ℝ => b * y) volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

lemma volume_planarStrip (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    volume (planarStrip a b) = ENNReal.ofReal (4 * a) := by
  have hc : Continuous (fun y : ℝ => 2 * (a + b * y)) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => 2 * (a + b * y)) (Icc (-1 : ℝ) 1) :=
    hc.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] (fun y => 2 * (a + b * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    dsimp
    nlinarith [mul_nonneg hb (show 0 ≤ y + 1 by linarith [hy.1])]
  rw [volume_planarStrip_eq_lintegral, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_strip_width]

lemma volume_symmDiff_centeredIntervals (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    volume (symmDiff (Icc (-r) r) (Icc (-s) s)) = ENNReal.ofReal (2 * |r - s|) := by
  have aux (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
      volume (symmDiff (Icc (-r) r) (Icc (-s) s)) = ENNReal.ofReal (2 * (s - r)) := by
    have hsub : Icc (-r) r ⊆ Icc (-s) s := Icc_subset_Icc (neg_le_neg hrs) hrs
    rw [symmDiff_of_le hsub, measure_sdiff hsub measurableSet_Icc.nullMeasurableSet]
    · rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub _ (by linarith : 0 ≤ r - -r)]
      congr 1
      ring
    · simp only [Real.volume_Icc, ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true]
  rcases le_total r s with hrs | hsr
  · rw [aux r s hr hrs, abs_of_nonpos (sub_nonpos.mpr hrs)]
    congr 1
    ring
  · rw [symmDiff_comm, aux s r hs hsr, abs_of_nonneg (sub_nonneg.mpr hsr)]

lemma integral_abs_unitInterval : (∫ y in Icc (-1 : ℝ) 1, |y|) = 1 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals
      (continuous_abs.intervalIntegrable (-1) 0) (continuous_abs.intervalIntegrable 0 1)]
  have hleft : (∫ y in (-1 : ℝ)..0, |y|) = ∫ y in (-1 : ℝ)..0, -y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy
    exact abs_of_nonpos hy.2
  have hright : (∫ y in (0 : ℝ)..1, |y|) = ∫ y in (0 : ℝ)..1, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    exact abs_of_nonneg hy.1
  rw [hleft, hright, intervalIntegral.integral_neg]
  norm_num

lemma volume_planarStrip_symmDiff (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    volume (symmDiff (planarStrip a 0) (planarStrip a b)) = ENNReal.ofReal (2 * b) := by
  have ha : 0 ≤ a := hb.trans hba
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm ((measurableSet_planarStrip a 0).symmDiff (measurableSet_planarStrip a b))]
  have hslices : (fun y : ℝ => volume ((fun x : ℝ => (x, y)) ⁻¹'
      symmDiff (planarStrip a 0) (planarStrip a b))) =
      (Icc (-1 : ℝ) 1).indicator (fun y => ENNReal.ofReal (2 * b * |y|)) := by
    funext y
    by_cases hy : y ∈ Icc (-1 : ℝ) 1
    · have hs0 : (fun x : ℝ => (x, y)) ⁻¹' planarStrip a 0 = Icc (-a) a := by
        ext x
        change (y ∈ Icc (-1 : ℝ) 1 ∧ |x| ≤ a + 0 * y) ↔ _
        simp only [hy, true_and, zero_mul, add_zero, mem_Icc, abs_le]
      have hsb : (fun x : ℝ => (x, y)) ⁻¹' planarStrip a b =
          Icc (-(a + b * y)) (a + b * y) := by
        ext x
        change (y ∈ Icc (-1 : ℝ) 1 ∧ |x| ≤ a + b * y) ↔ _
        simp only [hy, true_and, mem_Icc, abs_le]
      have hrad : 0 ≤ a + b * y := by
        nlinarith [mul_nonneg hb (show 0 ≤ y + 1 by linarith [hy.1])]
      rw [preimage_symmDiff, hs0, hsb, volume_symmDiff_centeredIntervals a (a + b * y) ha hrad,
        indicator_of_mem hy]
      congr 1
      rw [show a - (a + b * y) = -(b * y) by ring, abs_neg, abs_mul, abs_of_nonneg hb]
      ring
    · have hempty (c : ℝ) : (fun x : ℝ => (x, y)) ⁻¹' planarStrip a c = ∅ := by
        ext x
        change (y ∈ Icc (-1 : ℝ) 1 ∧ |x| ≤ a + c * y) ↔ False
        simp only [hy, false_and]
      rw [preimage_symmDiff, hempty 0, hempty b, symmDiff_self]
      change volume (∅ : Set ℝ) = _
      rw [measure_empty, indicator_of_notMem hy]
  rw [hslices, lintegral_indicator measurableSet_Icc]
  have hc : Continuous (fun y : ℝ => 2 * b * |y|) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => 2 * b * |y|) (Icc (-1 : ℝ) 1) :=
    hc.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] (fun y => 2 * b * |y|) :=
    Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (abs_nonneg y))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul, integral_abs_unitInterval,
    mul_one]

lemma planarStrip_subset_square (a b : ℝ) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    planarStrip a b ⊆ (Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1 := by
  intro p hp
  refine ⟨?_, hp.1⟩
  have hrad : a + b * p.2 ≤ 1 := by
    nlinarith [mul_nonneg hb (show 0 ≤ 1 - p.2 by linarith [hp.1.2])]
  exact abs_le.mp (hp.2.trans hrad)

/-- The positive outer cell of a planar affine strip, with null ties omitted. -/
def planarRightStrip (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-1 : ℝ) 1 ∧ p.1 ∈ Ioc (a + b * p.2) 1}

/-- The negative outer cell of a planar affine strip, with null ties omitted. -/
def planarLeftStrip (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-1 : ℝ) 1 ∧ p.1 ∈ Ico (-1) (-(a + b * p.2))}

lemma measurableSet_planarRightStrip (a b : ℝ) : MeasurableSet (planarRightStrip a b) := by
  unfold planarRightStrip
  measurability

lemma measurableSet_planarLeftStrip (a b : ℝ) : MeasurableSet (planarLeftStrip a b) := by
  unfold planarLeftStrip
  measurability

lemma volume_planarRightStrip_eq_lintegral (a b : ℝ) :
    volume (planarRightStrip a b) =
      ∫⁻ y in Icc (-1 : ℝ) 1, ENNReal.ofReal (1 - (a + b * y)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_planarRightStrip a b)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarRightStrip a b = Ioc (a + b * y) 1 := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ x ∈ Ioc (a + b * y) 1) ↔ _
      simp only [hy, true_and]
    rw [hs, Real.volume_Ioc, indicator_of_mem hy]
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarRightStrip a b = ∅ := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ x ∈ Ioc (a + b * y) 1) ↔ False
      simp only [hy, false_and]
    rw [hs, measure_empty, indicator_of_notMem hy]

lemma volume_planarLeftStrip_eq_lintegral (a b : ℝ) :
    volume (planarLeftStrip a b) =
      ∫⁻ y in Icc (-1 : ℝ) 1, ENNReal.ofReal (1 - (a + b * y)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_planarLeftStrip a b)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarLeftStrip a b = Ico (-1) (-(a + b * y)) := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ x ∈ Ico (-1) (-(a + b * y))) ↔ _
      simp only [hy, true_and]
    rw [hs, Real.volume_Ico, indicator_of_mem hy]
    congr 1
    ring
  · have hs : (fun x : ℝ => (x, y)) ⁻¹' planarLeftStrip a b = ∅ := by
      ext x
      change (y ∈ Icc (-1 : ℝ) 1 ∧ x ∈ Ico (-1) (-(a + b * y))) ↔ False
      simp only [hy, false_and]
    rw [hs, measure_empty, indicator_of_notMem hy]

lemma integral_affine_unitInterval (a b : ℝ) :
    (∫ y in Icc (-1 : ℝ) 1, a + b * y) = 2 * a := by
  have h := integral_strip_width a b
  rw [integral_const_mul] at h
  linarith

lemma integral_outerStrip_width (a b : ℝ) :
    (∫ y in Icc (-1 : ℝ) 1, 1 - (a + b * y)) = 2 * (1 - a) := by
  have hf : (fun y : ℝ => 1 - (a + b * y)) = (fun y => (1 - a) + (-b) * y) := by
    funext y
    ring
  rw [hf, integral_affine_unitInterval]

lemma lintegral_outerStrip_width (a b : ℝ) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (∫⁻ y in Icc (-1 : ℝ) 1, ENNReal.ofReal (1 - (a + b * y))) =
      ENNReal.ofReal (2 * (1 - a)) := by
  have hc : Continuous (fun y : ℝ => 1 - (a + b * y)) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => 1 - (a + b * y)) (Icc (-1 : ℝ) 1) :=
    hc.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] (fun y => 1 - (a + b * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    dsimp
    nlinarith [mul_nonneg hb (show 0 ≤ 1 - y by linarith [hy.2])]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_outerStrip_width]

lemma volume_planarRightStrip (a b : ℝ) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    volume (planarRightStrip a b) = ENNReal.ofReal (2 * (1 - a)) := by
  rw [volume_planarRightStrip_eq_lintegral, lintegral_outerStrip_width a b hb hab]

lemma volume_planarLeftStrip (a b : ℝ) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    volume (planarLeftStrip a b) = ENNReal.ofReal (2 * (1 - a)) := by
  rw [volume_planarLeftStrip_eq_lintegral, lintegral_outerStrip_width a b hb hab]

lemma planarRightStrip_subset_square (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    planarRightStrip a b ⊆ (Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1 := by
  intro p hp
  refine ⟨⟨?_, hp.2.2⟩, hp.1⟩
  have hrad : 0 ≤ a + b * p.2 := by
    nlinarith [mul_nonneg hb (show 0 ≤ p.2 + 1 by linarith [hp.1.1])]
  linarith [hp.2.1]

lemma planarLeftStrip_subset_square (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    planarLeftStrip a b ⊆ (Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1 := by
  intro p hp
  refine ⟨⟨hp.2.1, ?_⟩, hp.1⟩
  have hrad : 0 ≤ a + b * p.2 := by
    nlinarith [mul_nonneg hb (show 0 ≤ p.2 + 1 by linarith [hp.1.1])]
  linarith [hp.2.2]

private lemma central_inter_square (a b : ℝ) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    {p : ℝ × ℝ | |p.1| ≤ a + b * p.2} ∩
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = planarStrip a b := by
  ext p
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨hp.2, h⟩
  · intro hp
    exact ⟨hp.2, planarStrip_subset_square a b hb hab hp⟩

private lemma quarter_mul_ofReal (r : ℝ) :
    (4 : ℝ≥0∞)⁻¹ * ENNReal.ofReal r = ENNReal.ofReal (r / 4) := by
  have h : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [h, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- The closed tilted central cell has normalized cube mass `a`. -/
theorem uniformMeasure_cube_centralCell {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d) {x : E d | |x i| ≤ a + b * x j} =
      ENNReal.ofReal a := by
  change uniformMeasure (cube d)
    ((fun x : E d => (x i, x j)) ⁻¹' {p : ℝ × ℝ | |p.1| ≤ a + b * p.2}) = _
  rw [uniformMeasure_cube_coordPair_preimage i j hij _ (by measurability),
    central_inter_square a b hb hab, volume_planarStrip a b hb hba,
    quarter_mul_ofReal]
  congr 1
  ring

/-- Moving the central-cell boundary changes cube mass by `b/2`. -/
theorem uniformMeasure_cube_centralCell_symmDiff {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d)
      (symmDiff {x : E d | |x i| ≤ a} {x : E d | |x i| ≤ a + b * x j}) =
      ENNReal.ofReal (b / 2) := by
  have ha1 : a + 0 ≤ 1 := by linarith
  have heq : symmDiff {x : E d | |x i| ≤ a} {x : E d | |x i| ≤ a + b * x j} =
      (fun x : E d => (x i, x j)) ⁻¹'
        symmDiff {p : ℝ × ℝ | |p.1| ≤ a + 0 * p.2}
          {p : ℝ × ℝ | |p.1| ≤ a + b * p.2} := by
    rw [preimage_symmDiff]
    simp
  rw [heq, uniformMeasure_cube_coordPair_preimage i j hij _
    ((by measurability : MeasurableSet {p : ℝ × ℝ | |p.1| ≤ a + 0 * p.2}).symmDiff
      (by measurability)), inter_symmDiff_distrib_right,
    central_inter_square a 0 (le_refl 0) ha1,
    central_inter_square a b hb hab, volume_planarStrip_symmDiff a b hb hba,
    quarter_mul_ofReal]
  congr 1
  ring

/-- The positive outer cell of a tilted slab has mass `(1-a)/2`. -/
theorem uniformMeasure_cube_rightCell {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d) {x : E d | a + b * x j < x i} =
      ENNReal.ofReal ((1 - a) / 2) := by
  have hset : {p : ℝ × ℝ | a + b * p.2 < p.1} ∩
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = planarRightStrip a b := by
    ext p
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨hp.2, h, hp.1.2⟩
    · intro hp
      exact ⟨hp.2.1, planarRightStrip_subset_square a b hb hba hp⟩
  change uniformMeasure (cube d)
    ((fun x : E d => (x i, x j)) ⁻¹' {p : ℝ × ℝ | a + b * p.2 < p.1}) = _
  rw [uniformMeasure_cube_coordPair_preimage i j hij _ (by measurability), hset,
    volume_planarRightStrip a b hb hab, quarter_mul_ofReal]
  congr 1
  ring

/-- The negative outer cell of a tilted slab has mass `(1-a)/2`. -/
theorem uniformMeasure_cube_leftCell {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d) {x : E d | x i < -(a + b * x j)} =
      ENNReal.ofReal ((1 - a) / 2) := by
  have hset : {p : ℝ × ℝ | p.1 < -(a + b * p.2)} ∩
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = planarLeftStrip a b := by
    ext p
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨hp.2, hp.1.1, h⟩
    · intro hp
      exact ⟨hp.2.2, planarLeftStrip_subset_square a b hb hba hp⟩
  change uniformMeasure (cube d)
    ((fun x : E d => (x i, x j)) ⁻¹' {p : ℝ × ℝ | p.1 < -(a + b * p.2)}) = _
  rw [uniformMeasure_cube_coordPair_preimage i j hij _ (by measurability), hset,
    volume_planarLeftStrip a b hb hab, quarter_mul_ofReal]
  congr 1
  ring

end Problem358

end

end OAI
