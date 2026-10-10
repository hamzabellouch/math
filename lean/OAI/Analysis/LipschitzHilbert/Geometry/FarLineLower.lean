import OAI.Analysis.LipschitzHilbert.Geometry.FarStripGeometry

namespace OAI

/-! A lower bound for a transverse line average of the actual dilated
rectangle. The constants fit the fixed dilation in the selection rule. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem far_line_lower (R : Rectangle) (x w : Plane) (q : ℝ) (hq : 0 < q)
    (hqL : q ≤ R.long) (hw : ‖w‖ ≤ 1) (htrans : 1/2 ≤ |R.axes.repr w 1|)
    (hxL : |R.axes.repr (x-R.center) 0| ≤ 64*R.long)
    (hxW : |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*q) :
    ENNReal.ofReal (min R.short q) ≤
      ∫⁻ t in Icc (-64*q) (64*q),
        (R.dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w) := by
  let F := fun t : ℝ =>
    (R.dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w)
  have hF (t : ℝ) (ht : x+t • w ∈ (R.dilate 265 (by norm_num)).carrier) : F t = 1 := by
    exact indicator_of_mem ht _
  have hw0 : |R.axes.repr w 0| ≤ 1 := (R.abs_coordinate_le_norm w 0).trans hw
  have hw1 : |R.axes.repr w 1| ≤ 1 := (R.abs_coordinate_le_norm w 1).trans hw
  have hlong (t : ℝ) (ht : |t| ≤ 64*q) :
      |R.axes.repr (x+t • w-R.center) 0| ≤ 265*R.long/2 := by
    rw [line_coordinate]
    have hm : |t*R.axes.repr w 0| ≤ 64*q := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hw0 (abs_nonneg t)).trans (by simpa using ht)
    exact (abs_add_le _ _).trans (by linarith)
  by_cases hWq : R.short ≤ q
  · let A : Set ℝ := (fun t => R.axes.repr (x-R.center) 1+t*R.axes.repr w 1) ⁻¹'
        Icc (-R.short/2) (R.short/2)
    have hAm : MeasurableSet A := measurableSet_Icc.preimage (by fun_prop)
    have hsub : A ⊆ Icc (-64*q) (64*q) := by
      intro t ht
      have hu : |R.axes.repr (x-R.center) 1+t*R.axes.repr w 1| ≤ R.short/2 := by
        simpa only [A,mem_preimage,mem_Icc,neg_div,←abs_le] using ht
      have hb : |t*R.axes.repr w 1| ≤ R.short+8*q := by
        have h := abs_sub
          (R.axes.repr (x-R.center) 1+t*R.axes.repr w 1) (R.axes.repr (x-R.center) 1)
        simp only [add_sub_cancel_left] at h
        linarith
      have hprod := mul_le_mul_of_nonneg_left htrans (abs_nonneg t)
      rw [←abs_mul] at hprod
      have habs : |t| ≤ 64*q := by linarith
      simpa only [mem_Icc,neg_mul] using abs_le.mp habs
    have hmem (t : ℝ) (ht : t ∈ A) : x+t • w ∈ (R.dilate 265 (by norm_num)).carrier := by
      constructor
      · exact hlong t (by simpa only [mem_Icc,neg_mul,←abs_le] using hsub ht)
      · change |R.axes.repr (x+t • w-R.center) 1| ≤ 265*R.short/2
        rw [line_coordinate]
        have hu : |R.axes.repr (x-R.center) 1+t*R.axes.repr w 1| ≤ R.short/2 := by
          simpa only [A,mem_preimage,mem_Icc,neg_div,←abs_le] using ht
        linarith [R.short_pos]
    have hd : R.axes.repr w 1 ≠ 0 := by
      intro he
      rw [he,abs_zero] at htrans
      norm_num at htrans
    have hvol : ENNReal.ofReal R.short ≤ volume A := by
      have he : A = (fun t : ℝ => t*R.axes.repr w 1) ⁻¹'
          ((fun u : ℝ => R.axes.repr (x-R.center) 1+u) ⁻¹' Icc (-R.short/2) (R.short/2)) := rfl
      rw [he,Real.volume_preimage_mul_right hd,
        (measurePreserving_add_left volume _).measure_preimage measurableSet_Icc.nullMeasurableSet,
        Real.volume_Icc,show R.short/2- -R.short/2=R.short by ring]
      have hi : (1:ℝ) ≤ |(R.axes.repr w 1)⁻¹| := by
        rw [abs_inv]
        exact (one_le_inv₀ (abs_pos.mpr hd)).mpr hw1
      calc
        _ = 1*ENNReal.ofReal R.short := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi) le_rfl
    rw [min_eq_left hWq]
    calc
      _ ≤ volume A := hvol
      _ = ∫⁻ t in A, F t := by
        rw [setLIntegral_congr_fun hAm (fun t ht => hF t (hmem t ht))]
        simp
      _ ≤ _ := lintegral_mono_set hsub
  · have hqW : q ≤ R.short := le_of_not_ge hWq
    have hsub : Icc (-q/2) (q/2) ⊆ Icc (-64*q) (64*q) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2]
    have hmem (t : ℝ) (ht : t ∈ Icc (-q/2) (q/2)) :
        x+t • w ∈ (R.dilate 265 (by norm_num)).carrier := by
      have htq : |t| ≤ q/2 := by simpa only [mem_Icc,neg_div,←abs_le] using ht
      constructor
      · exact hlong t (by linarith)
      · change |R.axes.repr (x+t • w-R.center) 1| ≤ 265*R.short/2
        rw [line_coordinate]
        have hm : |t*R.axes.repr w 1| ≤ q/2 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left hw1 (abs_nonneg t)).trans (by simpa using htq)
        exact (abs_add_le _ _).trans (by linarith)
    rw [min_eq_right hqW]
    calc
      _ = volume (Icc (-q/2) (q/2)) := by rw [Real.volume_Icc]; congr 1; ring
      _ = ∫⁻ t in Icc (-q/2) (q/2), F t := by
        rw [setLIntegral_congr_fun measurableSet_Icc (fun t ht => hF t (hmem t ht))]
        simp
      _ ≤ _ := lintegral_mono_set hsub

end LipschitzHilbert.Rectangle

end

end OAI
