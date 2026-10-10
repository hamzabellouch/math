import OAI.Analysis.KadisonKastler.CharacterContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # A bounded analytic kernel for modular matrix coefficients

The factor `s` absorbs the possible growth of the logarithmic modular
phase on the closed KMS strip. No modular algebra invariance is used.
-/

namespace KadisonKastler

noncomputable section

def modularStripKernel (z : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) * Complex.exp ((-Complex.I * z) * (resolventLogFrequency s : ℂ))

theorem modularStripKernel_differentiable (s : ℝ) :
    Differentiable ℂ (fun z => modularStripKernel z s) := by
  unfold modularStripKernel
  fun_prop

theorem modularStripKernel_hasDerivAt (s : ℝ) (z : ℂ) :
    HasDerivAt (fun w => modularStripKernel w s)
      ((-Complex.I * (resolventLogFrequency s : ℂ)) * modularStripKernel z s) z := by
  have h : HasDerivAt (fun w : ℂ => (-Complex.I * w) * (resolventLogFrequency s : ℂ))
      (-Complex.I * (resolventLogFrequency s : ℂ)) z := by
    convert (hasDerivAt_const_mul (x := z) (-Complex.I * (resolventLogFrequency s : ℂ))) using 1
    funext w
    ring
  convert h.cexp.const_mul (s : ℂ) using 1 <;> unfold modularStripKernel <;> ring

theorem modularStripKernel_norm {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ‖modularStripKernel z s‖ = Real.exp
      ((1 - z.im) * Real.log s + z.im * Real.log (1 - s)) := by
  have hre : ((-Complex.I * z) * (resolventLogFrequency s : ℂ)).re =
      z.im * resolventLogFrequency s := by
    simp [Complex.mul_re, Complex.mul_im]
  calc
    _ = s * Real.exp (z.im * resolventLogFrequency s) := by
      rw [modularStripKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, Complex.norm_exp, hre]
    _ = Real.exp (Real.log s + z.im * resolventLogFrequency s) := by
      rw [Real.exp_add, Real.exp_log hs]
    _ = _ := by
      congr 1
      unfold resolventLogFrequency
      ring

theorem modularStripKernel_norm_le_one {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    ‖modularStripKernel z s‖ ≤ 1 := by
  rw [modularStripKernel_norm hs]
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1.le
  have hlog' : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hz1) hlog
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hz0 hlog'
  calc
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (add_nonpos h₁ h₂)
    _ = 1 := Real.exp_zero

end

end KadisonKastler

end OAI
