import OAI.NumberTheory.TwoPointCorrelations.PretentiousDistance
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre

noncomputable def mrtArchimedeanTwist (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

noncomputable def mrtPrimeEulerTerm (b : ℕ → ℂ) (t : ℝ) (p : ℕ) : ℂ :=
  (b p * conj (mrtArchimedeanTwist t p)) / (p : ℂ)

lemma mrtPrimeEulerTerm_norm_le (b : ℕ → ℂ) (t : ℝ) {p : ℕ}
    (_hp : 0 < p) (hb : ‖b p‖ ≤ 1) :
    ‖mrtPrimeEulerTerm b t p‖ ≤ (1 : ℝ) / p := by
  rw [mrtPrimeEulerTerm, norm_div, norm_mul, norm_conj,
    mrtArchimedeanTwist_norm, mul_one, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma mrtPrimeEulerTerm_re (b : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (mrtPrimeEulerTerm b t p).re = (b p * conj (mrtArchimedeanTwist t p)).re / p := by
  change (b p * conj (mrtArchimedeanTwist t p) / ((p : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]

/-- The finite Euler product retains the full pretentious-distance gain.
The remaining prime-square error is absolutely summable. -/
theorem mrt_finite_euler_distance_bound (b : ℕ → ℂ)
    (hb : ∀ n : ℕ, 0 < n → ‖b n‖ ≤ 1) (t : ℝ) (N : ℕ) :
    ‖∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm b t p)⁻¹‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖mrtPrimeEulerTerm b t p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le b t hprime.pos (hb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  have hs : (∑ p ∈ primesUpTo N,
      ((mrtPrimeEulerTerm b t p).re + (1 : ℝ) / (p : ℝ) ^ 2)) =
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [sum_add_distrib, squaredDistance, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    rw [mrtPrimeEulerTerm_re]
    ring
  rw [norm_prod, ← hs, Real.exp_sum]
  apply prod_le_prod₀
  · intro p _
    exact norm_nonneg _
  · intro p hp
    apply (mrt_local_euler_bound (hz p hp)).trans
    apply Real.exp_le_exp.mpr
    apply add_le_add le_rfl
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ ≤ ((1 : ℝ) / p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (mrtPrimeEulerTerm_norm_le b t hprime.pos
          (hb p hprime.pos)) 2
      _ = _ := by simp

/-- Multiplication by a real mask in `[0,1]` can reduce the squared
pretentious distance by at most a factor of two (MRT Lemma A.4(i)). -/
theorem mrt_masked_distance_lower (b twist : ℕ → ℂ) (mask : ℕ → ℝ) (N : ℕ)
    (hb : ∀ p ∈ primesUpTo N, ‖b p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1)
    (hmask : ∀ p ∈ primesUpTo N, 0 ≤ mask p ∧ mask p ≤ 1) :
    squaredDistance b twist N ≤
      2 * squaredDistance (fun p => b p * (mask p : ℂ)) twist N := by
  unfold squaredDistance
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
  have hz : ‖b p * conj (twist p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact (mul_le_mul (hb p hp) (htwist p hp) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hx1 : (b p * conj (twist p)).re ≤ 1 := (Complex.re_le_norm _).trans hz
  have hx0 : -1 ≤ (b p * conj (twist p)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (b p * conj (twist p)))).1
    linarith
  have he : (b p * (mask p : ℂ) * conj (twist p)).re =
      mask p * (b p * conj (twist p)).re := by
    rw [show b p * (mask p : ℂ) * conj (twist p) =
      (mask p : ℂ) * (b p * conj (twist p)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hp0.le
  rcases hmask p hp with ⟨hg0, hg1⟩
  by_cases hx : 0 ≤ (b p * conj (twist p)).re
  · have := mul_le_mul_of_nonneg_right hg1 hx
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hg0 (le_of_lt (lt_of_not_ge hx))
    linarith

end TwoPointCorrelations

end OAI
