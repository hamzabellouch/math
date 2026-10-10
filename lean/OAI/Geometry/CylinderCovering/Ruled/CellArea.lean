import OAI.Geometry.CylinderCovering.Ruled.CellGeometry

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ProductCells

private def cellHeight (A B x : ℝ) : ℝ := B / max (B/A) |x|

private lemma cellHeight_continuous {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Continuous (cellHeight A B) := by
  apply continuous_const.div (continuous_const.max continuous_abs)
  intro x
  exact ne_of_gt ((div_pos hB hA).trans_le (le_max_left _ _))

private lemma cellHeight_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (x : ℝ) :
    0 < cellHeight A B x :=
  div_pos hB ((div_pos hB hA).trans_le (le_max_left _ _))

private lemma cellHeight_small {A B x : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : |x| ≤ B/A) : cellHeight A B x = A := by
  unfold cellHeight
  rw [max_eq_left hx]
  field_simp

private lemma cellHeight_large {A B x : ℝ} (hx : B/A ≤ |x|) :
    cellHeight A B x = B/|x| := by
  simp only [cellHeight,max_eq_right hx]

private lemma abs_le_cellHeight_iff {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B) :
    |y| ≤ cellHeight A B x ↔ |y| ≤ A ∧ |x*y| ≤ B := by
  have hc : 0 < B/A := div_pos hB hA
  by_cases hx : |x| ≤ B/A
  · rw [cellHeight_small hA hB hx]
    constructor
    · intro hy
      refine ⟨hy,?_⟩
      rw [abs_mul]
      have hAx : |x| *A ≤ B := (le_div_iff₀ hA).mp hx
      nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg x)]
    · exact And.left
  · have hx' : B/A ≤ |x| := (lt_of_not_ge hx).le
    have hx0 : 0 < |x| := hc.trans_le hx'
    rw [cellHeight_large hx',le_div_iff₀ hx0]
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · have hAx : B ≤ |x| *A := (div_le_iff₀ hA).mp hx'
        have hym : |y| *|x| ≤ A*|x| := by nlinarith
        exact (mul_le_mul_iff_left₀ hx0).mp hym
      · rw [abs_mul]; nlinarith
    · intro h
      rw [abs_mul] at h
      nlinarith [h.2]

private lemma closedCell_eq_height {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    closedCell A B = {p : Plane | p.1 ∈ Icc (-A) A ∧
      p.2 ∈ Icc (-(cellHeight A B p.1)) (cellHeight A B p.1)} := by
  ext p
  simp only [closedCell,mem_ofPred_eq,mem_Icc,← abs_le,
    abs_le_cellHeight_iff hA hB]

private lemma integral_cellHeight_quadrant {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    (∫ x in (0:ℝ)..A, cellHeight A B x) = B*(1+Real.log (A^2/B)) := by
  have hc : 0 < B/A := div_pos hB hA
  have hcA : B/A ≤ A := (div_le_iff₀ hA).mpr (by nlinarith)
  have hint := cellHeight_continuous hA hB
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint.intervalIntegrable (0:ℝ) (B/A)) (hint.intervalIntegrable (B/A) A)]
  have hsmall : (∫ x in (0:ℝ)..(B/A), cellHeight A B x) = ∫ x in (0:ℝ)..(B/A), A := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hc.le] at hx
    exact cellHeight_small hA hB (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hlarge : (∫ x in (B/A)..A, cellHeight A B x) = ∫ x in (B/A)..A, B/x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hcA] at hx
    rw [cellHeight_large (by rw [abs_of_nonneg (hc.le.trans hx.1)]; exact hx.1),
      abs_of_nonneg (hc.le.trans hx.1)]
  rw [hsmall,hlarge,quadrant_integral A B hA hB]

private lemma integral_cellHeight_full {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    (∫ x in (-A)..A, cellHeight A B x) = 2*B*(1+Real.log (A^2/B)) := by
  have hint := cellHeight_continuous hA hB
  have heven : (∫ x in (-A)..(0:ℝ), cellHeight A B x) =
      ∫ x in (0:ℝ)..A, cellHeight A B x := by
    simpa [cellHeight,abs_neg] using
      (intervalIntegral.integral_comp_neg (f:=cellHeight A B) (a:=-A) (b:=0))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint.intervalIntegrable (-A) (0:ℝ)) (hint.intervalIntegrable (0:ℝ) A),
    heven,integral_cellHeight_quadrant hA hB hBA]
  ring

private lemma volume_closedCell_eq_region {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    volume (closedCell A B) = volume (regionBetween
      (fun x => -(cellHeight A B x)) (cellHeight A B) (Icc (-A) A)) := by
  have hc := cellHeight_continuous hA hB
  change ((volume : Measure ℝ).prod volume) _ = ((volume : Measure ℝ).prod volume) _
  rw [Measure.prod_apply (closedCell_isClosed A B).measurableSet,
    Measure.prod_apply (measurableSet_regionBetween (f:=fun x => -(cellHeight A B x)) hc.neg.measurable hc.measurable measurableSet_Icc)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Icc (-A) A
  · have h₁ : Prod.mk x ⁻¹' closedCell A B =
        Icc (-(cellHeight A B x)) (cellHeight A B x) := by
      rw [closedCell_eq_height hA hB]
      ext y
      simp only [mem_preimage,mem_ofPred_eq,hx,true_and]
    have h₂ : Prod.mk x ⁻¹' regionBetween
        (fun x => -(cellHeight A B x)) (cellHeight A B) (Icc (-A) A) =
        Ioo (-(cellHeight A B x)) (cellHeight A B x) := by
      ext y
      simp only [regionBetween,mem_preimage,mem_ofPred_eq,hx,true_and]
    rw [h₁,h₂]
    simp
  · have h₁ : Prod.mk x ⁻¹' closedCell A B = ∅ := by
      rw [closedCell_eq_height hA hB]
      ext y
      simp only [mem_preimage,mem_ofPred_eq,hx,false_and,mem_empty_iff_false]
    have h₂ : Prod.mk x ⁻¹' regionBetween
        (fun x => -(cellHeight A B x)) (cellHeight A B) (Icc (-A) A) = ∅ := by
      ext y
      simp only [regionBetween,mem_preimage,mem_ofPred_eq,hx,false_and,mem_empty_iff_false]
    rw [h₁,h₂]

theorem volume_closedCell {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume (closedCell A B) = ENNReal.ofReal (4*B*(1+Real.log (A^2/B))) := by
  have hc := cellHeight_continuous hA hB
  have hi : IntegrableOn (cellHeight A B) (Icc (-A) A) := hc.continuousOn.integrableOn_Icc
  rw [volume_closedCell_eq_region hA hB]
  change ((volume : Measure ℝ).prod volume) _ = _
  rw [volume_regionBetween_eq_integral (f:=fun x => -(cellHeight A B x)) hi.neg hi measurableSet_Icc
    (fun x _ => by have h := cellHeight_pos hA hB x; linarith)]
  congr 1
  change (∫ x in Icc (-A) A, cellHeight A B x - -cellHeight A B x) = _
  simp_rw [sub_neg_eq_add,← two_mul]
  rw [integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -A ≤ A by linarith),
    integral_cellHeight_full hA hB hBA]
  ring

theorem area_closedCell {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume.real (closedCell A B) = 4*B*(1+Real.log (A^2/B)) := by
  rw [Measure.real_def,volume_closedCell hA hB hBA,ENNReal.toReal_ofReal]
  have hlog : 0 ≤ Real.log (A^2/B) := Real.log_nonneg ((le_div_iff₀ hB).mpr (by nlinarith))
  positivity

private lemma abs_lt_cellHeight_iff {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B) :
    |y| < cellHeight A B x ↔ |y| < A ∧ |x*y| < B := by
  have hc : 0 < B/A := div_pos hB hA
  by_cases hx : |x| ≤ B/A
  · rw [cellHeight_small hA hB hx]
    constructor
    · intro hy
      refine ⟨hy,?_⟩
      rw [abs_mul]
      have h₁ := mul_le_mul_of_nonneg_right hx (abs_nonneg y)
      have h₂ := mul_lt_mul_of_pos_left hy hc
      have h₃ : (B/A)*A = B := div_mul_cancel₀ B (ne_of_gt hA)
      nlinarith
    · exact And.left
  · have hx' : B/A ≤ |x| := (lt_of_not_ge hx).le
    have hx0 : 0 < |x| := hc.trans_le hx'
    rw [cellHeight_large hx',lt_div_iff₀ hx0]
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · have hAx : B ≤ |x| * A := (div_le_iff₀ hA).mp hx'
        have hym : |y| * |x| < A*|x| := by nlinarith
        exact (mul_lt_mul_iff_left₀ hx0).mp hym
      · rw [abs_mul]; nlinarith
    · intro h
      rw [abs_mul] at h
      nlinarith [h.2]

private lemma openCell_eq_region {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    openCell A B = regionBetween (fun x => -(cellHeight A B x))
      (cellHeight A B) (Ioo (-A) A) := by
  ext p
  simp only [openCell,regionBetween,mem_ofPred_eq,mem_Ioo,← abs_lt,
    abs_lt_cellHeight_iff hA hB]

theorem volume_openCell {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume (openCell A B) = ENNReal.ofReal (4*B*(1+Real.log (A^2/B))) := by
  have hc := cellHeight_continuous hA hB
  have hi : IntegrableOn (cellHeight A B) (Ioo (-A) A) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [openCell_eq_region hA hB]
  change ((volume : Measure ℝ).prod volume) _ = _
  rw [volume_regionBetween_eq_integral (f:=fun x => -(cellHeight A B x))
    hi.neg hi measurableSet_Ioo (fun x _ => by have h := cellHeight_pos hA hB x; linarith)]
  congr 1
  change (∫ x in Ioo (-A) A, cellHeight A B x - -cellHeight A B x) = _
  simp_rw [sub_neg_eq_add,← two_mul]
  rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -A ≤ A by linarith),
    integral_cellHeight_full hA hB hBA]
  ring

theorem area_openCell {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume.real (openCell A B) = 4*B*(1+Real.log (A^2/B)) := by
  rw [Measure.real_def,volume_openCell hA hB hBA,ENNReal.toReal_ofReal]
  have hlog : 0 ≤ Real.log (A^2/B) := Real.log_nonneg ((le_div_iff₀ hB).mpr (by nlinarith))
  positivity

theorem geometric_area_ratio {tau gamma : ℝ}
    (htau : 0 < tau) (htau1 : tau < 1) (hg : 0 ≤ gamma)
    (hpad : (1+gamma)*tau < 1) :
    volume.real (interceptCell tau gamma) / volume.real (parameterCell tau) =
      areaRatio tau gamma := by
  have hc : 0 < 1+gamma := by linarith
  have hB : 0 < (1+gamma)*tau := mul_pos hc htau
  have hlog : 0 ≤ Real.log (1/tau) := Real.log_nonneg ((le_div_iff₀ htau).mpr (by linarith))
  have hden : 1+Real.log (1/tau) ≠ 0 := by linarith
  unfold interceptCell parameterCell
  rw [area_openCell (by norm_num : (0:ℝ)<3) hB (by nlinarith),
    area_closedCell (by norm_num : (0:ℝ)<1) htau (by nlinarith)]
  unfold areaRatio
  norm_num
  field_simp

lemma volume_closedCell_sdiff_openCell {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume (closedCell A B \ openCell A B) = 0 := by
  have hf : volume (openCell A B) ≠ ⊤ := by
    rw [volume_openCell hA hB hBA]
    exact ENNReal.ofReal_ne_top
  rw [measure_sdiff (openCell_subset_closedCell A B)
    (openCell_isOpen A B).measurableSet.nullMeasurableSet hf,
    volume_closedCell hA hB hBA,volume_openCell hA hB hBA,tsub_self]

lemma volume_frontier_closedCell {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume (frontier (closedCell A B)) = 0 := by
  apply measure_mono_null _ (volume_closedCell_sdiff_openCell hA hB hBA)
  intro p hp
  refine ⟨(closedCell_isClosed A B).frontier_subset hp,?_⟩
  intro hop
  exact hp.2 (((openCell_isOpen A B).subset_interior_iff.mpr
    (openCell_subset_closedCell A B)) hop)

lemma volume_frontier_openCell {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A^2) :
    volume (frontier (openCell A B)) = 0 := by
  apply measure_mono_null _ (volume_closedCell_sdiff_openCell hA hB hBA)
  intro p hp
  refine ⟨closure_minimal (openCell_subset_closedCell A B) (closedCell_isClosed A B) hp.1,?_⟩
  intro hop
  exact hp.2 (by simpa only [(openCell_isOpen A B).interior_eq] using hop)

theorem geometry_proof : GeometryStatement := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro A B hA hB hBA
    exact ⟨closedCell_isCompact A B,openCell_isOpen A B,openCell_isBounded A B,
      area_closedCell hA hB hBA,area_openCell hA hB hBA,
      volume_frontier_closedCell hA hB hBA,volume_frontier_openCell hA hB hBA⟩
  · intro m gamma hm
    have hm0 : 0 < m := by linarith
    exact ⟨logarithmicCell_eq_dilation m hm0,logarithmicIntercept_eq_dilation m gamma hm0⟩
  · exact ⟨fun _ _ => geometric_area_ratio,areaRatio_tendsto_zero⟩
  · exact ⟨fun _ _ => exists_parameter_after_padding,
      fun _ _ => exists_padding_after_parameter,fun _ => exists_logarithmic_parameters⟩
  · intro z tau gamma eps s e hz hs he₁ he₂ heps hgap
    exact expanded_parameterCell_mem_intercept hz hs he₁ he₂ heps hgap

end ProductCells

end

end OAI
