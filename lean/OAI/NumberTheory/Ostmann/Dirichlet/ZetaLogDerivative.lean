import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Analysis.LocalZeroLogDerivative
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaDerivativePreparation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem uniform_regularZeta_neg_real_log_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (-logDeriv regularZeta s).re ≤ C * Real.log (|s.im| + 6) := by
  classical
  obtain ⟨C, hC, hlocal⟩ :=
    Erdos970.Erdos970Dependency.SiegelWalfisz.exists_local_zero_log_derivative_constant
  obtain ⟨K, hK, hbound⟩ := exists_normalizedZeta_bound
  have hlogK := Real.log_nonneg hK
  refine ⟨C * (Real.log K + 2), mul_pos hC (by positivity), ?_⟩
  intro s hs hs2
  let t : ℝ := s.im
  let w : ℂ := ((4 / 5 * (s.re - 2) : ℝ) : ℂ)
  have hw : ‖w‖ ≤ 17 / 20 := by
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4 / 5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have heval : zetaDiskPoint t w = s := by
    rw [zetaDiskPoint_ofReal]
    exact Complex.re_add_im s
  have hn := regularZeta_ne_zero_of_one_le_re (s := zetaCenter t) (by simp)
  have hne : regularZeta (zetaDiskPoint t w) ≠ 0 := by
    rw [heval]
    exact regularZeta_ne_zero_of_one_le_re hs.le
  obtain ⟨S, hS, hb⟩ := hlocal (K * (|t| + 6) ^ 2) (zeta_envelope_gt_one hK t)
    (normalizedZeta t) (fun z _ => normalizedZeta_analytic t z)
    (normalizedZeta_zero t) (fun z hz => hbound t z
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
  have hzeros (z : ℂ) : normalizedZeta t z = 0 ↔ regularZeta (zetaDiskPoint t z) = 0 := by
    unfold normalizedZeta
    exact div_eq_zero_iff.trans (or_iff_left hn)
  have hb' := hb w hw (fun hz => hne ((hzeros w).mp hz))
  rw [normalizedZeta_log_derivative t w hne] at hb'
  have hsum : 0 ≤ (∑ rho ∈ S,
      (analyticOrderAt (normalizedZeta t) rho).toNat / (w - rho) : ℂ).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro rho hr
    have hre := (normalizedZeta_zero_re_lt t ((hS rho).mp hr).2).le.trans hwre.le
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
      Complex.sub_re]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hre))
      (Complex.normSq_nonneg _)
  have herror := (Complex.re_le_norm (-((5 / 4 : ℂ) *
      (deriv regularZeta (zetaDiskPoint t w) / regularZeta (zetaDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedZeta t) rho).toNat / (w - rho)))).trans
    (by simpa only [norm_neg] using hb')
  have hscale (a : ℂ) : ((5 / 4 : ℂ) * a).re = (5 / 4 : ℝ) * a.re := by
    norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale, heval] at herror
  have hlift := mul_le_mul_of_nonneg_left (log_zeta_envelope_bound hK t) hC.le
  have hpositive : 0 ≤ C * (Real.log K + 2) * Real.log (|t| + 6) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by have := abs_nonneg t; linarith)
  simp only [logDeriv_apply, Complex.neg_re]
  change -(deriv regularZeta s / regularZeta s).re ≤ _
  change _ ≤ C * (Real.log K + 2) * Real.log (|t| + 6)
  nlinarith

theorem exists_zeta_all_height_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (-logDeriv riemannZeta s).re ≤
        C * Real.log (|s.im| + 6) + (1 / (s - 1)).re := by
  obtain ⟨C, hC, hb⟩ := uniform_regularZeta_neg_real_log_derivative
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  rw [neg_logDeriv_zeta_pole_split hs, Complex.add_re]
  exact add_le_add (hb s hs hs2) le_rfl

end Ostmann.Dirichlet

end OAI
