import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroPenalty
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaLocalZeros

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem uniform_regularZeta_zero_penalty :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 7/8 ≤ beta → beta < 1 →
      regularZeta ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      (-deriv (regularZeta) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        regularZeta ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
        C * (Real.log (|t|+6)) - 1/(sigma-beta) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := uniform_zeta_local_zero_estimates
  refine ⟨C, hC, ?_⟩
  intro sigma beta t hs hs2 hb34 hb1 hzero
  obtain ⟨S, hS, hSre, _, hbound⟩ := hlocal t
  let w : ℂ := ((4/5*(sigma-2):ℝ):ℂ)
  let rho0 : ℂ := ((4/5*(beta-2):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((4/5*(sigma-2):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hr : ‖rho0‖ ≤ 19/20 := by
    change ‖((4/5*(beta-2):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4/5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have hrL : regularZeta (zetaDiskPoint t rho0) = 0 := by
    rw [zetaDiskPoint_ofReal]
    exact hzero
  have hrmem : rho0 ∈ S := (hS rho0).mpr ⟨hr, hrL⟩
  have hrNorm : normalizedZeta t rho0 = 0 := by
    unfold normalizedZeta
    rw [hrL, zero_div]
  have hm := normalizedZeta_zero_order_pos t hrNorm
  have hden : 0 < sigma-beta := by linarith
  have hsub : w-rho0 = ((4/5*(sigma-beta):ℝ):ℂ) := by
    dsimp only [w, rho0]
    push_cast
    ring
  have hterm : (5/4:ℝ)/(sigma-beta) ≤
      (((analyticOrderAt (normalizedZeta t) rho0).toNat:ℂ)/(w-rho0)).re := by
    rw [hsub]
    rw [show ((analyticOrderAt (normalizedZeta t) rho0).toNat:ℂ) =
      (((analyticOrderAt (normalizedZeta t) rho0).toNat:ℝ):ℂ) by simp]
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1/(4/5*(sigma-beta)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  have hsum : (5/4:ℝ)/(sigma-beta) ≤
      (∑ rho ∈ S, (analyticOrderAt (normalizedZeta t) rho).toNat / (w-rho):ℂ).re := by
    rw [Complex.re_sum]
    apply hterm.trans
    exact Finset.single_le_sum (fun rho hr => real_zero_term_nonneg (analyticOrderAt (normalizedZeta t) rho).toNat ((hSre rho hr).le.trans hwre.le)) hrmem
  have hn : regularZeta (zetaDiskPoint t w) ≠ 0 := by
    rw [zetaDiskPoint_ofReal]
    exact regularZeta_ne_zero_of_one_le_re (by simpa using hs.le)
  have h := hbound w hw hn
  have herror := (Complex.re_le_norm (-(
    (5/4:ℂ) * (deriv (regularZeta) (zetaDiskPoint t w) /
      regularZeta (zetaDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedZeta t) rho).toNat / (w-rho)))).trans
    (by simpa only [norm_neg] using h)
  have hscale (a:ℂ) : ((5/4:ℂ)*a).re = (5/4:ℝ)*a.re := by norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale] at herror
  have hpos : 0 ≤ C * Real.log (|t| + 6) :=
    mul_nonneg hC.le (zero_le_one.trans (zeta_height_ge_one t))
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = zetaDiskPoint t w from (zetaDiskPoint_ofReal sigma t).symm,
    neg_div, Complex.neg_re]
  rw [div_eq_mul_inv] at hsum
  rw [one_div]
  nlinarith only [herror, hsum, hpos]

end Ostmann.Dirichlet

end OAI
