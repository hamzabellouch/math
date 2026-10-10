import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Fourier.BinKernel

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

theorem binL2Norm_ne_top (μ : Measure ℝ) [IsFiniteMeasure μ] {w : ℝ} (hw : 0 < w) :
    binL2Norm μ w ≠ ∞ := by
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ne_of_lt ((real_bin_collision_bound μ hw).trans_lt (measure_lt_top _ _)))

theorem binKernelConstant_pos : 0 < binKernelConstant := by
  have weight_pos : 0 < binKernelWeight 0 := by norm_num [binKernelWeight]
  exact weight_pos.trans_le (ENNReal.le_tsum 0)

theorem real_bin_shifted_self_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have h := real_bin_shifted_band_bound μ μ hw C s₀
  rw [binL2Norm_mul_self] at h
  exact h.trans (mul_le_mul_right (real_bin_collision_bound μ hw) _)

theorem real_bin_decaying_self_kernel_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod μ) ≤
      binKernelConstant * (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have h := real_bin_decaying_kernel_bound μ μ hw
  rw [binL2Norm_mul_self] at h
  exact h.trans (mul_le_mul_right (real_bin_collision_bound μ hw) _)

end PlanarFalconer

end OAI
