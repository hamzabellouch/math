import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroQuotientDisk

namespace OAI

/-! # Normalized logarithmic bounds after removing all zeros in a disk -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finite_zero_quotient_normalized_log (f g : ℂ → ℂ) (S : Finset ℂ)
    (R M : ℝ) (hR : 0 < R) (hM : 0 < M) (hf0 : f 0 ≠ 0)
    (hS : ∀ w ∈ S, ‖w‖ ≤ 2 * R)
    (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, f s = finiteZeroPolynomial f S s * g s)
    (hf : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖f z‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (2 * R)) (hgz : g z ≠ 0) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ Real.log M +
      (∑ w ∈ S, (analyticOrderNatAt f w : ℝ)) * Real.log 2 - Real.log ‖f 0‖ := by
  let N := ∑ w ∈ S, analyticOrderNatAt f w
  have hgne : g 0 ≠ 0 := by
    intro h
    exact hf0 (by rw [he, h, mul_zero])
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hgne
  have hfn : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hp : ‖finiteZeroPolynomial f S 0‖ ≤ (2 * R) ^ N := by
    apply finiteZeroPolynomial_norm_le f S 0 (2 * R) (by positivity)
    intro w hw
    simpa only [zero_sub, norm_neg] using hS w hw
  have hb : ‖f 0‖ ≤ (2 * R) ^ N * ‖g 0‖ := by
    rw [he 0, norm_mul]
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have hu := finite_zero_quotient_disk_bound f g S R M hR hM.le hS hg he hf z
    (closedBall_subset_closedBall (by linarith) hz)
  have hm : ‖g z‖ * ‖f 0‖ ≤ M * 2 ^ N * ‖g 0‖ := by
    calc
      _ ≤ (M / R ^ N) * ((2 * R) ^ N * ‖g 0‖) :=
        mul_le_mul hu hb hfn.le (div_nonneg hM.le (pow_nonneg hR.le _))
      _ = _ := by
        rw [mul_pow]
        field_simp [hR.ne']
  have hratio : ‖g z‖ / ‖g 0‖ ≤ (M * 2 ^ N) / ‖f 0‖ :=
    (div_le_div_iff₀ hgn hfn).mpr hm
  have hzn : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
  rw [← Real.log_div hzn.ne' hgn.ne']
  apply (Real.log_le_log (div_pos hzn hgn) hratio).trans_eq
  rw [Real.log_div (by positivity) hfn.ne', Real.log_mul hM.ne' (by positivity), Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
