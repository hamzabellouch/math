import OAI.Analysis.LipschitzHilbert.Estimates.ErrorSourceBridge
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarPositiveConvolution

namespace OAI

/-! Exact planar convolution interpretation of each constructed line
error source, including scalar normalization. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_const_mul (l W c : ℝ) (f : ℝ × ℝ → ℝ) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => c*f z) x y =
      c * planarPositiveConvolution l W f x y := by
  unfold planarPositiveConvolution
  simp_rw [mul_left_comm _ c, integral_const_mul]

theorem actualErrorSources_term_eq {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2:ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) (j : Fin N) (x : ℝ) :
    (actualErrorSources J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).term j x =
      planarPositiveConvolution (topLength/(2:ℝ)^j.val) W
        (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
          (a*(2:ℝ)^j.val) |direction p-t|) x y := by
  have hf : Measurable (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|) := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hb (p : ℝ × ℝ) : ‖A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|‖ ≤ A*(1+c) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA
      (errorSourceProfile_nonneg _ _ _ _ (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hc
      (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)) hA
  exact (planarPositiveConvolution_eq_iterated _ _ _ hf
    (div_pos hL (pow_pos (by norm_num) _)) hW hb x y).symm

end LipschitzHilbert

end

end OAI
