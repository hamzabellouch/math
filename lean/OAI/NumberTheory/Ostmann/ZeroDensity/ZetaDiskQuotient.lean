import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaDiskZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.SmallDiskLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroPolynomialLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroQuotientDisk

namespace OAI

/-! # Removing the actual local zeta zeros, with a logarithmic error -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zeta_disk_quotient_exists (t : ℝ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z) ∧
      (∀ z ∈ closedBall 0 (3 / 2 : ℝ), g z ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := remove_finite_analytic_zeros (zetaAtHeight t)
    (zetaAtHeight_analytic t) (zetaAtHeight_order_ne_top t) (zetaDiskZeros t)
  refine ⟨g, hg, he, ?_⟩
  intro z hz
  by_cases hS : z ∈ zetaDiskZeros t
  · exact hne z hS
  · intro hzero
    apply hS
    apply (mem_zetaDiskZeros t z).mpr
    exact ⟨by simpa using hz, by rw [he, hzero, mul_zero]⟩

theorem zeta_disk_quotient_bound (t M : ℝ) (hM : 32 * (|t| + 2) ^ 2 ≤ M)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z)
    (z : ℂ) (hz : ‖z‖ ≤ 7 / 4) :
    ‖g z‖ ≤ M * 4 ^ (∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w) := by
  let N := ∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w
  have hb : ∀ u ∈ sphere (0 : ℂ) (7 / 4), ‖g u‖ ≤ M * 4 ^ N := by
    intro u hu
    have hnu : ‖u‖ = 7 / 4 := by simpa using hu
    have hp : (1 / 4 : ℝ) ^ N ≤ ‖finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) u‖ := by
      apply finiteZeroPolynomial_norm_ge _ _ _ _ (by norm_num)
      intro w hw
      have hnw := ((mem_zetaDiskZeros t w).mp hw).1
      have htri := norm_le_norm_sub_add u w
      linarith
    have hm := (zetaAtHeight_disk_bound t u hnu.le).trans hM
    rw [he, norm_mul] at hm
    have hprod := (mul_le_mul_of_nonneg_right hp (norm_nonneg (g u))).trans hm
    have hh := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) N)).mpr
      (by simpa only [mul_comm] using hprod)
    simpa only [one_div, inv_pow, div_inv_eq_mul] using hh
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (7 / 4)) isBounded_ball
  · exact DiffContOnCl.mk_ball (fun u _ => (hg u).differentiableAt.differentiableWithinAt)
      (fun u _ => (hg u).continuousAt.continuousWithinAt)
  · rw [frontier_ball (0 : ℂ) (by norm_num : (7 / 4 : ℝ) ≠ 0)]
    exact hb
  · simpa [closure_ball (0 : ℂ) (by norm_num : (7 / 4 : ℝ) ≠ 0)] using hz

theorem zeta_disk_quotient_log_bound (t M : ℝ) (hM : 32 * (|t| + 2) ^ 2 ≤ M)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z)
    (hne : ∀ z ∈ closedBall 0 (3 / 2 : ℝ), g z ≠ 0)
    (z : ℂ) (hz : ‖z‖ ≤ 3 / 2) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ Real.log (3 * M) +
      (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) * Real.log 6 := by
  let N := ∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w
  have hMp : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hgc : 0 < ‖g 0‖ := norm_pos_iff.mpr (hne 0 (mem_closedBall_self (by norm_num)))
  have hp : ‖finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) 0‖ ≤ (3 / 2 : ℝ) ^ N := by
    apply finiteZeroPolynomial_norm_le _ _ _ _ (by norm_num)
    intro w hw
    simpa only [zero_sub, norm_neg] using ((mem_zetaDiskZeros t w).mp hw).1
  have hlo : (1 / 3 : ℝ) ≤ (3 / 2 : ℝ) ^ N * ‖g 0‖ := by
    have hh := zetaAtHeight_lower_zero t
    rw [he, norm_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hpow : (4 : ℝ) ^ N * (3 / 2 : ℝ) ^ N = 6 ^ N := by rw [← mul_pow]; norm_num
  have hm : M * 4 ^ N ≤ 3 * M * 6 ^ N * ‖g 0‖ := by
    calc
      _ = (3 * M * 4 ^ N) * (1 / 3) := by ring
      _ ≤ (3 * M * 4 ^ N) * ((3 / 2) ^ N * ‖g 0‖) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = 3 * M * (4 ^ N * (3 / 2) ^ N) * ‖g 0‖ := by ring
      _ = _ := by rw [hpow]
  have hu := zeta_disk_quotient_bound t M hM g hg he z (by linarith)
  have hratio : ‖g z‖ / ‖g 0‖ ≤ 3 * M * 6 ^ N := (div_le_iff₀ hgc).mpr (hu.trans hm)
  have hgz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z (by simpa using hz))
  rw [← Real.log_div hgz.ne' hgc.ne']
  apply (Real.log_le_log (div_pos hgz hgc) hratio).trans_eq
  rw [Real.log_mul (by positivity : 3 * M ≠ 0) (by positivity : (6 : ℝ) ^ N ≠ 0), Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
