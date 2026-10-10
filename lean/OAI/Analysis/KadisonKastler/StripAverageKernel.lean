import OAI.Analysis.KadisonKastler.FourierLaplace

namespace OAI

/-! # The decaying scalar kernel for modular strip averaging -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def stripAverageKernel (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(z * (t : ℂ))) / (Real.exp (a * t) + Real.exp (-a * t) : ℝ)

theorem stripAverageKernel_continuous (a : ℝ) (z : ℂ) :
    Continuous (stripAverageKernel a z) := by
  unfold stripAverageKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact_mod_cast (add_pos (Real.exp_pos (a * t)) (Real.exp_pos (-a * t))).ne'

theorem stripAverageKernel_hasDerivAt (a t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => stripAverageKernel a w t)
      (-(t : ℂ) * stripAverageKernel a z t) z := by
  have hd : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) z := by
    convert! ((hasDerivAt_id z).mul_const (t : ℂ)).neg using 1
    simp
  unfold stripAverageKernel
  convert hd.cexp.div_const (Real.exp (a * t) + Real.exp (-a * t) : ℝ) using 1
  ring

theorem stripAverageKernel_norm (a t : ℝ) (z : ℂ) :
    ‖stripAverageKernel a z t‖ =
      Real.exp (-z.re * t) / (Real.exp (a * t) + Real.exp (-a * t)) := by
  unfold stripAverageKernel
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
  congr 2
  simp

theorem stripAverageKernel_decay (a t : ℝ) (z : ℂ) :
    ‖stripAverageKernel a z t‖ ≤ Real.exp (-(a - |z.re|) * |t|) := by
  rw [stripAverageKernel_norm]
  have hd : 0 < Real.exp (a * t) + Real.exp (-a * t) := by positivity
  have hden : Real.exp (a * |t|) ≤ Real.exp (a * t) + Real.exp (-a * t) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos ht]
      have he : a * -t = -a * t := by ring
      rw [he]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hnum : Real.exp (-z.re * t) ≤ Real.exp (|z.re| * |t|) := by
    apply Real.exp_le_exp.mpr
    calc
      -z.re * t ≤ |-z.re * t| := le_abs_self _
      _ = |z.re| * |t| := by rw [abs_mul, abs_neg]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ Real.exp (|z.re| * |t|) := hnum
    _ = Real.exp (-(a - |z.re|) * |t|) * Real.exp (a * |t|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

theorem stripAverageKernel_integrable {a : ℝ} {z : ℂ} (hz : |z.re| < a) :
    Integrable (stripAverageKernel a z) := by
  apply (integrable_laplaceKernel (sub_pos.mpr hz)).norm.mono'
    (stripAverageKernel_continuous a z).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa only [laplaceKernel, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul] using
      stripAverageKernel_decay a t z

end

end KadisonKastler

end OAI
