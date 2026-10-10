import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace OAI

/-! # Uniform estimates for the exponential inverse near zero

These elementary Banach-algebra estimates are used to recover a small
normalizer's infinitesimal generator inside its invariant algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A]

/-- A bound independent of the algebra and of commutation of the two elements. -/
theorem norm_pow_succ_sub_pow_succ_le (x y : A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1 : ℝ) * r ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y := by
      rw [pow_succ x (n + 1), pow_succ y (n + 1)]
      noncomm_ring
    calc
      _ ≤ ‖x ^ (n + 1)‖ * ‖x - y‖ + ‖x ^ (n + 1) - y ^ (n + 1)‖ * ‖y‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ r ^ (n + 1) * ‖x - y‖ + ((n + 1 : ℝ) * r ^ n * ‖x - y‖) * r := by
        gcongr
        exact (norm_pow_le' x (Nat.succ_pos n)).trans (pow_le_pow_left₀ (norm_nonneg x) hx _)
      _ = (↑(n + 1) + 1 : ℝ) * r ^ (n + 1) * ‖x - y‖ := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- Differentiating a positive-degree exponential coefficient never gives
an absolute value larger than one. -/
theorem exponential_derivative_coefficient_le_one (n : ℕ) :
    ((n + 1 : ℝ) / (n + 1).factorial) ≤ 1 := by
  have hp : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  apply (div_le_one hp).mpr
  exact_mod_cast Nat.self_le_factorial (n + 1)

section ComplexAlgebra

variable [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The exponential after removing its constant and linear terms. -/
def exponentialRemainder (x : A) : A := NormedSpace.exp x - 1 - x

theorem hasSum_exponentialRemainder (x : A) :
    HasSum (fun n : ℕ => ((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2))
      (exponentialRemainder x) := by
  have h := (hasSum_nat_add_iff' 2).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  simpa [exponentialRemainder, Finset.sum_range_succ, sub_add_eq_sub_sub] using h

omit [CompleteSpace A] in
theorem norm_exponential_term_sub_le (x y : A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2) -
      ((n + 2).factorial⁻¹ : ℂ) • y ^ (n + 2)‖ ≤ r ^ (n + 1) * ‖x - y‖ := by
  have hc : ((n + 2 : ℝ) / (n + 2).factorial) ≤ 1 := by
    have h := exponential_derivative_coefficient_le_one (n + 1)
    norm_num [Nat.cast_add, add_assoc] at h ⊢
    exact h
  have hp : ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤
      (n + 2 : ℝ) * r ^ (n + 1) * ‖x - y‖ := by
    have h := norm_pow_succ_sub_pow_succ_le x y hr hx hy (n + 1)
    norm_num [Nat.cast_add, add_assoc] at h ⊢
    exact h
  calc
    _ = ((n + 2).factorial : ℝ)⁻¹ * ‖x ^ (n + 2) - y ^ (n + 2)‖ := by
      rw [← smul_sub, norm_smul]
      simp
    _ ≤ ((n + 2).factorial : ℝ)⁻¹ *
        ((n + 2 : ℝ) * r ^ (n + 1) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((n + 2 : ℝ) / (n + 2).factorial) * (r ^ (n + 1) * ‖x - y‖) := by ring
    _ ≤ 1 * (r ^ (n + 1) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := one_mul _

theorem norm_exponentialRemainder_sub_le (x y : A) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖exponentialRemainder x - exponentialRemainder y‖ ≤
      r / (1 - r) * ‖x - y‖ := by
  let f := fun n : ℕ => ((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2) -
    ((n + 2).factorial⁻¹ : ℂ) • y ^ (n + 2)
  let b := fun n : ℕ => r ^ (n + 1) * ‖x - y‖
  have hf : HasSum f (exponentialRemainder x - exponentialRemainder y) :=
    (hasSum_exponentialRemainder x).sub (hasSum_exponentialRemainder y)
  have hb : HasSum b (r / (1 - r) * ‖x - y‖) := by
    simpa [b, pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hasSum_geometric_of_lt_one hr hr1).mul_left r).mul_right ‖x - y‖
  have hbound (n : ℕ) : ‖f n‖ ≤ b n := norm_exponential_term_sub_le x y hr hx hy n
  rw [← hf.tsum_eq, ← hb.tsum_eq]
  exact (norm_tsum_le_tsum_norm (hb.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound)).trans
    (Summable.tsum_le_tsum hbound
      (hb.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound) hb.summable)

end ComplexAlgebra

end

end KadisonKastler

end OAI
