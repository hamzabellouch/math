import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRoot
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! The complex momentum differs from the positive real momentum by at most
|gamma|/sqrt(x). This is the pointwise estimate behind the bounded action error. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_re_nonneg (z : ℂ) : 0≤(Complex.sqrt z).re := by
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem spectralComplexSqrt_approx (x gamma : ℝ) (hx : 0<x) :
    ‖Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))-(Real.sqrt x : ℂ)‖≤
      |gamma|/Real.sqrt x := by
  let p := Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))
  let s := Real.sqrt x
  have hs : 0<s := Real.sqrt_pos.mpr hx
  have hp := spectralComplexSqrt_sq ((x : ℂ)+Complex.I*(gamma : ℂ))
  have hsC : (s : ℂ)^2=(x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx.le
  have hre : 0≤ p.re := spectralComplexSqrt_re_nonneg _
  have hsum : s≤‖p+(s : ℂ)‖ := by
    have hh := Complex.re_le_norm (p+(s : ℂ))
    simp only [Complex.add_re,Complex.ofReal_re] at hh
    linarith
  have he : (p-(s : ℂ))*(p+(s : ℂ))=Complex.I*(gamma : ℂ) := by
    change p^2=(x : ℂ)+Complex.I*(gamma : ℂ) at hp
    linear_combination hp-hsC
  have hn : ‖p-(s : ℂ)‖*‖p+(s : ℂ)‖=|gamma| := by
    have hh := congrArg norm he
    simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] using hh
  apply (le_div_iff₀ hs).mpr
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg (p-(s : ℂ)))).trans_eq hn

end DefocusingNLS

end OAI
