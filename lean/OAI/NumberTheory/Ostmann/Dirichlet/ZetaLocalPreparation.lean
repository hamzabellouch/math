import OAI.NumberTheory.Ostmann.Dirichlet.EntireJensen
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaDerivativePreparation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma zeta_height_ge_one (t : ℝ) : 1 ≤ Real.log (|t| + 6) := by
  have ht : 0 < |t| + 6 := by positivity
  exact ((Real.lt_log_iff_exp_lt ht).mpr
    (Real.exp_one_lt_three.trans (by have := abs_nonneg t; linarith))).le

lemma zeta_height_double_le (t : ℝ) :
    Real.log (|2 * t| + 6) ≤ 2 * Real.log (|t| + 6) := by
  have ht := abs_nonneg t
  have h := Real.log_le_log (by positivity : 0 < |2 * t| + 6)
    (show |2 * t| + 6 ≤ (|t| + 6) ^ 2 by rw [abs_mul]; norm_num; nlinarith)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  exact h

lemma regularZeta_eq_mul {s : ℂ} (hs : s ≠ 1) :
    regularZeta s = (s - 1) * riemannZeta s := by
  rw [regularZeta, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

lemma normalizedZeta_zero_order_pos (t : ℝ) {rho : ℂ}
    (hz : normalizedZeta t rho = 0) :
    1 ≤ (analyticOrderAt (normalizedZeta t) rho).toNat := by
  have htop : analyticOrderAt (normalizedZeta t) rho ≠ ⊤ := by
    intro h
    have he : normalizedZeta t = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho (normalizedZeta_analytic t)).mp h
    have hh := congrFun he 0
    rw [normalizedZeta_zero] at hh
    norm_num at hh
  exact ENat.toNat_pos ((normalizedZeta_analytic t rho).analyticOrderAt_ne_zero.mpr hz) htop

end Ostmann.Dirichlet

end OAI
