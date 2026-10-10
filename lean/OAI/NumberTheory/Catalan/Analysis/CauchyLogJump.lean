import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace InternalCatalan

theorem complex_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw,
    Complex.ofReal_sub]
  ring

theorem complex_log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw,
    Complex.ofReal_add]
  ring

def cauchyLogLeft (T : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * (Complex.log (Complex.I * (T : ℂ) - z) -
    Complex.log (-Complex.I * (T : ℂ) - z))

def cauchyLogRight (T : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * (Complex.log (z - Complex.I * (T : ℂ)) -
    Complex.log (z + Complex.I * (T : ℂ)))

theorem cauchyLogLeft_sub_cauchyLogRight {T : ℝ} {z : ℂ}
    (hlo : -T < z.im) (hhi : z.im < T) :
    cauchyLogLeft T z - cauchyLogRight T z = 2 * (Real.pi : ℂ) := by
  have ha : 0 < (Complex.I * (T : ℂ) - z).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    linarith
  have hb : (-Complex.I * (T : ℂ) - z).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, neg_mul, one_mul, zero_add]
    linarith
  have hnegA : z - Complex.I * (T : ℂ) = -(Complex.I * (T : ℂ) - z) := by ring
  have hnegB : z + Complex.I * (T : ℂ) = -(-Complex.I * (T : ℂ) - z) := by ring
  unfold cauchyLogLeft cauchyLogRight
  rw [hnegA, hnegB, complex_log_neg_of_im_pos ha, complex_log_neg_of_im_neg hb]
  calc
    _ = -(2 * (Real.pi : ℂ)) * (Complex.I * Complex.I) := by ring
    _ = 2 * (Real.pi : ℂ) := by rw [Complex.I_mul_I]; ring

theorem cauchyLogLeft_sub_cauchyLogRight_of_abs_im_lt {T : ℝ} {z : ℂ}
    (hz : |z.im| < T) :
    cauchyLogLeft T z - cauchyLogRight T z = 2 * (Real.pi : ℂ) :=
  cauchyLogLeft_sub_cauchyLogRight (abs_lt.mp hz).1 (abs_lt.mp hz).2

end InternalCatalan

end

end OAI
