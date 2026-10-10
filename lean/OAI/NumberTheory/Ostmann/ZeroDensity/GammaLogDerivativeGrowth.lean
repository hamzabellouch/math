import Mathlib.NumberTheory.Harmonic.GammaDeriv
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaRealLogDerivative

namespace OAI

/-! # Divergence of the Gamma logarithmic derivative at positive integers -/

namespace Ostmann

open Complex Filter
open scoped Topology

theorem gamma_logDeriv_nat (n : ℕ) :
    logDeriv Complex.Gamma ((n : ℂ) + 1) =
      (-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℂ) := by
  rw [logDeriv_apply, Complex.deriv_Gamma_nat, Complex.Gamma_nat_eq_factorial]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_div_cancel_left₀ _ hn]
  push_cast
  rfl

theorem gamma_logDeriv_nat_re_tendsto :
    Tendsto (fun n : ℕ => (logDeriv Complex.Gamma ((n : ℂ) + 1)).re) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have h1 := Real.tendsto_harmonic_sub_log.eventually
    (lt_mem_nhds (show Real.eulerMascheroniConstant - 1 < Real.eulerMascheroniConstant by linarith))
  have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (b + 1)
  filter_upwards [h1, h2] with n hn hn'
  simp only [Function.comp_apply] at hn'
  rw [gamma_logDeriv_nat]
  simp only [add_re, neg_re, ofReal_re]
  linarith

end Ostmann

end OAI
