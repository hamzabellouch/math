import Mathlib.Analysis.Complex.RemovableSingularity
import OAI.NumberTheory.Ostmann.Characters.CharacterRightHalfPlane
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

namespace OAI

/-! # Removing the zeta pole and bounding the resulting entire function -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

noncomputable def regularizedZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

@[simp] theorem regularizedZeta_one : regularizedZeta 1 = 1 := by simp [regularizedZeta]

theorem regularizedZeta_eq (s : ℂ) (hs : s ≠ 1) :
    regularizedZeta s = (s - 1) * riemannZeta s := by
  simp [regularizedZeta, hs]

theorem regularizedZeta_analytic (s : ℂ) : AnalyticAt ℂ regularizedZeta s := by
  have hoff (z : ℂ) (hz : z ≠ 1) : AnalyticAt ℂ regularizedZeta z := by
    have he : regularizedZeta =ᶠ[𝓝 z] (fun w => (w - 1) * riemannZeta w) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact regularizedZeta_eq w hw
    exact ((analyticAt_id.sub analyticAt_const).mul (analyticOn_riemannZeta z hz)).congr he.symm
  by_cases hs : s = 1
  · subst s
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hoff z hz).differentiableAt
    · exact continuousAt_update_same.mpr riemannZeta_residue_one
  · exact hoff s hs

theorem regularizedZeta_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : regularizedZeta s ≠ 0 := by
  by_cases he : s = 1
  · simp [he]
  · rw [regularizedZeta_eq s he]
    exact mul_ne_zero (sub_ne_zero.mpr he) (riemannZeta_ne_zero_of_one_le_re hs)

theorem regularizedZeta_logDeriv (s : ℂ) (hs : 1 < s.re) :
    logDeriv regularizedZeta s = (s - 1)⁻¹ + logDeriv riemannZeta s := by
  have hne : s ≠ 1 := by intro he; simp [he] at hs
  have he : regularizedZeta =ᶠ[𝓝 s] ((fun z : ℂ => z - 1) * riemannZeta) := by
    filter_upwards [isOpen_ne.mem_nhds hne] with z hz
    exact regularizedZeta_eq z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s
      (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re hs.le)
      (differentiableAt_id.sub_const _) (differentiableAt_riemannZeta hne)]
  simp [logDeriv_apply]

theorem regularizedZeta_norm_bound (s : ℂ) (hs : 1 / 4 ≤ s.re) :
    ‖regularizedZeta s‖ ≤ ‖s - 1‖ + 1 + 4 * ‖s - 1‖ * ‖s‖ := by
  by_cases he : s = 1
  · simp [he]
  · have hdomain : s ∈ zetaAbelContinuationDomain := ⟨he, by
      change (1 / 10 : ℝ) < s.re
      linarith⟩
    have hb := norm_zetaAbelContinuationFormula_le s hdomain
    rw [← riemannZeta_eq_zetaAbelContinuationFormula s hdomain] at hb
    rw [regularizedZeta_eq s he, norm_mul]
    have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    have hsr : 0 < s.re := by linarith
    have hc : ‖s‖ / s.re ≤ 4 * ‖s‖ := by
      apply (div_le_iff₀ hsr).mpr
      nlinarith [norm_nonneg s]
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (s - 1))
    rw [one_div, norm_inv, mul_add, mul_add, mul_one, mul_inv_cancel₀ hn.ne'] at hm
    nlinarith [mul_le_mul_of_nonneg_left hc (norm_nonneg (s - 1))]

end Ostmann

end OAI
