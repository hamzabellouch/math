import OAI.MeasureTheory.Falconer.Geometry.BinOffsets
import Mathlib.Analysis.PSeries

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

noncomputable def binKernelWeight (h : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (4/((h:ℝ)+1/2)^2)

noncomputable def binKernelConstant : ℝ≥0∞ := ∑' h : ℤ, binKernelWeight h

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end PlanarFalconer

end OAI
