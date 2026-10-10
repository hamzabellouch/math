import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Numerical bounds for the constructed common tracial position -/

namespace KadisonKastler

theorem commonPosition_tolerance_lt {γ : ℝ} (hγ : 0 < γ)
    (hsmall : γ < 174 / 1000000000000000) :
    69000000000 * γ < 50948 * Real.sqrt γ := by
  have hs := Real.sq_sqrt hγ.le
  have hr := Real.sqrt_nonneg γ
  have hs' : Real.sqrt γ < 1 / 2000000 := by nlinarith
  have hc : 69000000000 * Real.sqrt γ < 50948 := by linarith
  have h := mul_lt_mul_of_pos_right hc (Real.sqrt_pos.mpr hγ)
  nlinarith

end KadisonKastler

end OAI
