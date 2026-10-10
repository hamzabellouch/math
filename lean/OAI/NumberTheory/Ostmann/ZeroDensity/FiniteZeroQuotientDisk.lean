import Mathlib.Analysis.Complex.AbsMax
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteAnalyticZeroFactors

namespace OAI

/-! # Scaled disk bounds for finite zero removal -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finiteZeroPolynomial_norm_le (f : ℂ → ℂ) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (_hr : 0 ≤ r) (hS : ∀ w ∈ S, ‖z - w‖ ≤ r) :
    ‖finiteZeroPolynomial f S z‖ ≤ r ^ (∑ w ∈ S, analyticOrderNatAt f w) := by
  simp only [finiteZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hS w hw) _)

theorem finiteZeroPolynomial_norm_ge (f : ℂ → ℂ) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ w ∈ S, r ≤ ‖z - w‖) :
    r ^ (∑ w ∈ S, analyticOrderNatAt f w) ≤ ‖finiteZeroPolynomial f S z‖ := by
  simp only [finiteZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hr _)
    (fun w hw => pow_le_pow_left₀ hr (hS w hw) _)

/-- The annulus between radii 2R and 3R separates the removed zeros from
 the circle on which the original function is estimated. -/
theorem finite_zero_quotient_disk_bound (f g : ℂ → ℂ) (S : Finset ℂ)
    (R M : ℝ) (hR : 0 < R) (_hM : 0 ≤ M)
    (hS : ∀ w ∈ S, ‖w‖ ≤ 2 * R)
    (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, f s = finiteZeroPolynomial f S s * g s)
    (hf : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall (0 : ℂ) (3 * R),
      ‖g z‖ ≤ M / R ^ (∑ w ∈ S, analyticOrderNatAt f w) := by
  let N := ∑ w ∈ S, analyticOrderNatAt f w
  have hb : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖g z‖ ≤ M / R ^ N := by
    intro z hz
    have hnorm : ‖z‖ = 3 * R := by simpa using hz
    have hp : R ^ N ≤ ‖finiteZeroPolynomial f S z‖ := by
      apply finiteZeroPolynomial_norm_ge f S z R hR.le
      intro w hw
      have ht := norm_add_le (z - w) w
      rw [sub_add_cancel] at ht
      linarith [hS w hw]
    have hfm := hf z hz
    rw [he, norm_mul] at hfm
    apply (le_div_iff₀ (pow_pos hR N)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hfm
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (3 * R))
    isBounded_ball (f := g)
  · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
      (fun w _ => (hg w).continuousAt.continuousWithinAt)
  · rw [frontier_ball (0 : ℂ) (by positivity : 3 * R ≠ 0)]
    exact hb
  · rwa [closure_ball (0 : ℂ) (by positivity : 3 * R ≠ 0)]

end Ostmann

end OAI
