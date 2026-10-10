import Mathlib.Analysis.Complex.AbsMax
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeroSet

namespace OAI

/-! # Modulus bounds after removing the finite zero factors -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem characterZeroPolynomial_norm_le (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (_hr : 0 ≤ r) (hS : ∀ w ∈ S, ‖z - w‖ ≤ r) :
    ‖characterZeroPolynomial χ S z‖ ≤ r ^ (∑ w ∈ S, analyticOrderNatAt χ.L w) := by
  simp only [characterZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hS w hw) _)

theorem characterZeroPolynomial_norm_ge (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ w ∈ S, r ≤ ‖z - w‖) :
    r ^ (∑ w ∈ S, analyticOrderNatAt χ.L w) ≤ ‖characterZeroPolynomial χ S z‖ := by
  simp only [characterZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hr _)
    (fun w hw => pow_le_pow_left₀ hr (hS w hw) _)

/-- The removed quotient is nonvanishing on the whole smaller disk. -/
theorem character_contour_quotient_exists (χ : PrimitiveComplexCharacter) (t : ℝ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s) ∧
      (∀ s ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ), g s ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := character_remove_finite_zeros χ (characterContourZeros χ t)
  refine ⟨g, hg, he, ?_⟩
  intro s hs
  by_cases hz : s ∈ characterContourZeros χ t
  · exact hne s hz
  · intro hh
    have hf : χ.L s = 0 := by rw [he, hh, mul_zero]
    exact hz ((mem_characterContourZeros χ t s).mpr ⟨hs, hf⟩)

/-- A fixed annular reserve bounds the analytic quotient throughout the outer
 disk, even when the original L-function vanishes inside it. -/
theorem character_contour_quotient_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (_hM : 0 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (g : ℂ → ℂ) (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s) :
    ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ),
      ‖g z‖ ≤ M * 8 ^ (∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w) := by
  let N := ∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w
  have hb : ∀ z ∈ sphere (characterZeroCenter t) (11 / 4 : ℝ), ‖g z‖ ≤ M * 8 ^ N := by
    intro z hz
    have hdist : ‖z - characterZeroCenter t‖ = 11 / 4 := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have hlower : (1 / 8 : ℝ) ^ N ≤ ‖characterZeroPolynomial χ (characterContourZeros χ t) z‖ := by
      apply characterZeroPolynomial_norm_ge χ _ z (1 / 8) (by norm_num)
      intro w hw
      have hw' := ((mem_characterContourZeros χ t w).mp hw).1
      have hdw : ‖w - characterZeroCenter t‖ ≤ 21 / 8 := by
        simpa only [mem_closedBall, dist_eq_norm] using hw'
      have hh := norm_sub_le (z - w) (characterZeroCenter t - w)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (characterZeroCenter t)] at hh
      linarith
    have hnorm := hbound z (sphere_subset_closedBall hz)
    rw [he z, norm_mul] at hnorm
    have hprod : (1 / 8 : ℝ) ^ N * ‖g z‖ ≤ M :=
      (mul_le_mul_of_nonneg_right hlower (norm_nonneg _)).trans hnorm
    have hh := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 1 / 8) N)).mpr (by simpa only [mul_comm] using hprod)
    simpa only [one_div, inv_pow, div_inv_eq_mul] using hh
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (characterZeroCenter t) (11 / 4)) isBounded_ball (f := g)
  · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
      (fun w _ => (hg w).continuousAt.continuousWithinAt)
  · rw [frontier_ball (characterZeroCenter t) (by norm_num : (11 / 4 : ℝ) ≠ 0)]
    exact hb
  · rwa [closure_ball (characterZeroCenter t) (by norm_num : (11 / 4 : ℝ) ≠ 0)]

end Ostmann

end OAI
