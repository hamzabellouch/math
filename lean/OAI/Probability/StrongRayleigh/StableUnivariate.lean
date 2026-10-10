import Mathlib

namespace OAI

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem aeval_root_im_eq_zero_of_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (z : ℂ) (hz : aeval z p = 0) : z.im = 0 := by
  have hle : z.im ≤ 0 := by
    by_contra! h
    exact hstable z h hz
  have hge : 0 ≤ z.im := by
    by_contra! h
    have hconj : aeval (conj z) p = 0 := by
      rw [Polynomial.aeval_conj, hz, map_zero]
    exact hstable (conj z) (by simpa using neg_pos.mpr h) hconj
  exact le_antisymm hle hge

theorem splits_of_upper_halfplane_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0) : p.Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ)
      (IsAlgClosed.splits _)
  intro z hz
  have heval : aeval z p = 0 := by
    simpa only [Polynomial.IsRoot, eval_map, aeval_def, eval₂_at_apply] using
      (Polynomial.isRoot_of_mem_roots hz)
  have him := aeval_root_im_eq_zero_of_stable p hstable z heval
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [him]

theorem eval_pos_of_nonnegative_coefficients (p : ℝ[X])
    (hp : p ≠ 0) (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    {t : ℝ} (ht : 0 < t) : 0 < p.eval t := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos
  · intro n hn
    exact mul_pos (lt_of_le_of_ne (hcoeff n)
      (Ne.symm (Polynomial.mem_support_iff.mp hn))) (pow_pos ht n)
  · exact Polynomial.support_nonempty.mpr hp

theorem aeval_root_re_nonpos_of_nonnegative_coefficients (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (z : ℂ) (hz : aeval z p = 0) : z.re ≤ 0 := by
  have hp : p ≠ 0 := by
    intro h
    have := hstable Complex.I (by simp)
    simp [h] at this
  have him := aeval_root_im_eq_zero_of_stable p hstable z hz
  have hreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  by_contra! hpos
  have heval : p.eval z.re = 0 := by
    have hc : ((p.eval z.re : ℝ) : ℂ) = 0 := by
      calc
        ((p.eval z.re : ℝ) : ℂ) = aeval (z.re : ℂ) p :=
          (Polynomial.aeval_ofReal (K := ℂ) p z.re).symm
        _ = 0 := by rw [hreal]; exact hz
    exact_mod_cast hc
  have := eval_pos_of_nonnegative_coefficients p hp hcoeff hpos
  linarith

theorem aeval_ne_zero_on_slitPlane_of_stable (p : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z p ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) : aeval z p ≠ 0 := by
  intro hzero
  rcases hz with hre | him
  · exact (not_lt_of_ge
      (aeval_root_re_nonpos_of_nonnegative_coefficients p hstable hcoeff z hzero)) hre
  · exact him (aeval_root_im_eq_zero_of_stable p hstable z hzero)

end Problem336AdditiveD139

end

end OAI
