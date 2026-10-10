import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Jacobsthal.Primes.RieszMellinKernel
import OAI.NumberTheory.Ostmann.Dirichlet.EntireJensen
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.LogZeroFree
import OAI.NumberTheory.Ostmann.Dirichlet.PrincipalHeightBound
import OAI.NumberTheory.Ostmann.Dirichlet.ZeroKernelComparison
import OAI.NumberTheory.Ostmann.Reuse.SiegelGap

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem uniform_real_log_derivative_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
        (deriv (DirichletCharacter.LFunction chi) (sigma : ℂ) /
          DirichletCharacter.LFunction chi (sigma : ℂ)).re ≤ K * modulusHeight q 0 := by
  classical
  obtain ⟨c, hc, hregion⟩ := exists_nonprincipal_log_zero_free_region
  obtain ⟨C, hC, hlocal⟩ := uniform_dirichlet_local_log_derivative
  obtain ⟨Cr, hCr, hright⟩ := uniform_log_derivative_right
  let d : ℝ := min c (1 / 4)
  have hd : 0 < d := lt_min hc (by norm_num)
  have hdc : d ≤ c := min_le_left _ _
  have hd4 : d ≤ 1 / 4 := min_le_right _ _
  let R : ℝ := 2 / d + Cr
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨2 * R + 2 * C, by positivity, ?_⟩
  intro q _ chi hchi sigma hs hs2
  let H : ℝ := modulusHeight q 0
  have hH : 1 ≤ H := modulusHeight_ge_one q 0
  have hHp : 0 < H := by linarith
  let x : ℝ := d / (2 * H)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxd : x ≤ d := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
    nlinarith
  have hsig0 : 1 < 1 + x := by linarith
  have hsig02 : 1 + x ≤ 2 := by linarith
  let D : ℝ → ℂ := fun u => deriv (DirichletCharacter.LFunction chi) (u : ℂ) /
    DirichletCharacter.LFunction chi (u : ℂ)
  have hright0 : ‖D (1 + x)‖ ≤ R * H := by
    have h := hright q chi ((1 + x : ℝ) : ℂ) (by simpa using hsig0)
    have he : ((1 + x) - 1)⁻¹ = (2 / d) * H := by
      rw [add_sub_cancel_left]
      dsimp only [x]
      field_simp
    simp only [Complex.ofReal_re] at h
    rw [he] at h
    have hh := mul_le_mul_of_nonneg_left hH hCr
    dsimp only [D, R] at *
    nlinarith only [h, hh]
  have hRnonneg : 0 ≤ R * H := mul_nonneg hR.le hHp.le
  by_cases hsmall : sigma ≤ 1 + x
  · obtain ⟨S, hS, _, hb⟩ := hlocal q chi hchi 0
    let w : ℝ → ℂ := fun u => ((2 / 5 * (u - 3) : ℝ) : ℂ)
    let Z : ℝ → ℂ := fun u => ∑ rho ∈ S,
      (analyticOrderAt (normalizedDirichlet chi 0) rho).toNat / (w u - rho)
    have herror (u : ℝ) (hu : 1 < u) (hu2 : u ≤ 2) :
        |(5 / 2 : ℝ) * (D u).re - (Z u).re| ≤ C * H := by
      have hw : ‖w u‖ ≤ 17 / 20 := by
        dsimp only [w]
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hn : DirichletCharacter.LFunction chi (dirichletDiskPoint 0 (w u)) ≠ 0 := by
        rw [dirichletDiskPoint_ofReal]
        simp only [Complex.ofReal_zero, zero_mul, add_zero]
        exact LFunction_ne_zero_right chi (by simpa using hu)
      have hh := (Complex.abs_re_le_norm _).trans (hb (w u) hw hn)
      have he : dirichletDiskPoint 0 (w u) = (u : ℂ) := by
        rw [dirichletDiskPoint_ofReal]
        simp
      have hscale (z : ℂ) : ((5 / 2 : ℂ) * z).re = (5 / 2 : ℝ) * z.re := by
        norm_num [Complex.mul_re]
      rw [Complex.sub_re, hscale, he] at hh
      exact hh
    have hcompare : (Z sigma).re ≤ 2 * (Z (1 + x)).re := by
      dsimp only [Z]
      rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro rho hrho
      obtain ⟨hrnorm, hrzero⟩ := (hS rho).mp hrho
      have hheight := modulusHeight_diskPoint_le q 0 hrnorm
      have hZp : 0 < modulusHeight q (dirichletDiskPoint 0 rho).im :=
        zero_lt_one.trans_le (modulusHeight_ge_one q _)
      have hdrop : x ≤ c / modulusHeight q (dirichletDiskPoint 0 rho).im := by
        calc
          _ ≤ c / (2 * H) := div_le_div_of_nonneg_right hdc (by positivity)
          _ ≤ _ := div_le_div_of_nonneg_left hc.le hZp hheight
      have hzeroRe : (dirichletDiskPoint 0 rho).re <
          1 - c / modulusHeight q (dirichletDiskPoint 0 rho).im := by
        by_contra! h
        exact hregion q chi hchi _ h hrzero
      rw [dirichletDiskPoint_re] at hzeroRe
      apply real_zero_term_le_mul _ (by nlinarith) (by linarith)
        (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith only [hzeroRe, hdrop, hs, hsmall]
    have he0 := (abs_le.mp (herror (1 + x) hsig0 hsig02)).1
    have he := (abs_le.mp (herror sigma hs hs2)).2
    have hD0 := (Complex.re_le_norm (D (1 + x))).trans hright0
    have hCH : 0 ≤ C * H := mul_nonneg hC.le hHp.le
    change (D sigma).re ≤ (2 * R + 2 * C) * H
    nlinarith only [he0, he, hcompare, hD0, hCH, hRnonneg]
  · have hinv : (sigma - 1)⁻¹ ≤ x⁻¹ :=
      inv_anti₀ hx (by linarith)
    have he : x⁻¹ = (2 / d) * H := by dsimp only [x]; field_simp
    rw [he] at hinv
    have h := hright q chi (sigma : ℂ) (by simpa using hs)
    simp only [Complex.ofReal_re] at h
    have hD := Complex.re_le_norm (D sigma)
    have hh := mul_le_mul_of_nonneg_left hH hCr
    have hCH : 0 ≤ C * H := mul_nonneg hC.le hHp.le
    change (D sigma).re ≤ (2 * R + 2 * C) * H
    change ‖D sigma‖ ≤ (sigma - 1)⁻¹ + Cr at h
    dsimp only [R] at *
    nlinarith only [h, hD, hinv, hh, hCH, hRnonneg]

end Ostmann.Dirichlet

end OAI
