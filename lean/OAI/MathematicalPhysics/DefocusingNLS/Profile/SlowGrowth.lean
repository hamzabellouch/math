import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowHigherDerivatives

namespace OAI

/-! # Polynomial bounds for the slow solution and all its derivatives -/

open Polynomial

namespace DefocusingNLS

theorem regularizedSlowSolution_polynomial_bound (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖regularizedSlowSolution q m x‖ ≤ C * ‖x‖ ^ (max (-q.re) 0) := by
  obtain ⟨A, hA, hbound⟩ := regularizedSlowSolution_first_remainder q m hq
  refine ⟨Real.exp (Real.pi * |q.im|) * (A + 1), by positivity, ?_⟩
  intro x hx hxnorm
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hxnorm).ne'
  have hnorm : ‖x ^ q * regularizedSlowSolution q m x‖ ≤ A + 1 := by
    calc
      _ ≤ ‖x ^ q * regularizedSlowSolution q m x - 1‖ + 1 := by
        simpa only [norm_one] using norm_le_norm_sub_add
          (x ^ q * regularizedSlowSolution q m x) 1
      _ ≤ A / ‖x‖ + 1 := add_le_add (hbound x hx hxnorm) le_rfl
      _ ≤ A + 1 := add_le_add (div_le_self hA hxnorm) le_rfl
  have hp : x ^ (-q) * (x ^ q * regularizedSlowSolution q m x) =
      regularizedSlowSolution q m x := by
    rw [← mul_assoc, ← Complex.cpow_add _ _ hx0, neg_add_cancel, Complex.cpow_zero, one_mul]
  have hpow := norm_cpow_le_rpow_max x (-q) hxnorm
  simp only [Complex.neg_im, abs_neg, Complex.neg_re] at hpow
  calc
    _ = ‖x ^ (-q)‖ * ‖x ^ q * regularizedSlowSolution q m x‖ := by rw [← norm_mul, hp]
    _ ≤ (Real.exp (Real.pi * |q.im|) * ‖x‖ ^ (max (-q.re) 0)) * (A + 1) :=
      mul_le_mul hpow hnorm (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem iteratedDeriv_regularizedSlowSolution_polynomial_bound
    (n : ℕ) (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖iteratedDeriv n (regularizedSlowSolution q m) x‖ ≤
        C * ‖x‖ ^ (max (-(q + n).re) 0) := by
  have hq' : -1 < (q + n).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨A, hA, hbound⟩ := regularizedSlowSolution_polynomial_bound (q + n) (m + n) hq'
  refine ⟨‖(-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q‖ * A, mul_nonneg (norm_nonneg _) hA, ?_⟩
  intro x hx hxnorm
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hxnorm).ne'
  rw [iteratedDeriv_regularizedSlowSolution_closed n q m x hq hx hx0, norm_mul]
  calc
    _ ≤ ‖(-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q‖ *
        (A * ‖x‖ ^ (max (-(q + n).re) 0)) :=
      mul_le_mul_of_nonneg_left (hbound x hx hxnorm) (norm_nonneg _)
    _ = _ := by ring

end DefocusingNLS

end OAI
