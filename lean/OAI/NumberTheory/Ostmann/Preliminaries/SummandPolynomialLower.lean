import OAI.NumberTheory.Ostmann.Preliminaries.SummandPolynomialBootstrap

namespace OAI

/-! # A concrete positive-power lower bound at twelfth powers -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_polynomial_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      (t : ℝ) ^ 3 ≤ ((summandPrefix A (t ^ 12)).card : ℝ) := by
  have htend : Tendsto (fun t : ℕ => t ^ 12) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    (constant_log_linear_small 48 (by norm_num))
  filter_upwards [h.symm.summand_polynomial_bootstrap hA,
    htend.eventually h.coverage_product_lower, hsmall,
    eventually_ge_atTop (2 : ℕ)] with t hu hl hs ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  let a : ℝ := (summandPrefix A (t ^ 12)).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hlogs : 4 * Real.log ((t ^ 12 : ℕ) : ℝ) ≤ t := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    change 48 * (1 + Real.log (t : ℝ)) ≤ (t : ℝ) at hs
    linarith
  have hlogp : 0 < 4 * Real.log ((t ^ 12 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    positivity
  have hp : (t : ℝ) ^ 12 ≤ a * (t : ℝ) ^ 8 * (4 * Real.log ((t ^ 12 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ hlogp).mp
    simpa only [Nat.cast_pow] using hl.trans (mul_le_mul_of_nonneg_left hu ha)
  have hh : (t : ℝ) ^ 12 ≤ a * (t : ℝ) ^ 8 * t :=
    hp.trans (mul_le_mul_of_nonneg_left hlogs (mul_nonneg ha (pow_nonneg htp.le 8)))
  have hcancel : (t : ℝ) ^ 9 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 9 * a := by
    calc
      _ = (t : ℝ) ^ 12 := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos htp 9)).mp hcancel

end Ostmann

end OAI
