import OAI.NumberTheory.Ostmann.Characters.SquarePullbackNorm
import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicResidueSum

namespace OAI

/-! # The uniform small-kernel bound for a weighted quadratic sum -/

namespace Ostmann

open scoped BigOperators

/-- The cutoff may include a complex quadratic phase. Only its absolute
bound enters this estimate, while the interval covers at least one period. -/
theorem small_kernel_quadratic_sum_bound (q W : ℕ) [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (weight : ℕ → ℂ) (B C N : ℝ)
    (hB : 0 ≤ B) (hN : 0 < N)
    (hq : (q : ℝ) ≤ N) (hW : (W : ℝ) ≤ C * N)
    (hw : ∀ w ∈ Finset.Ioc 0 W, ‖weight w‖ ≤ B) :
    ‖(N : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W, g (a * (w : ZMod q) ^ 2) * weight w‖ ≤
      B * (C + 1) * Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let D := Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hperiod := periodic_residue_sum_le q W (fun x => ‖g (a * x ^ 2)‖)
    (fun x => norm_nonneg _)
  have hnorm := square_pullback_norm_le q g hg henergy a
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W, g (a * (w : ZMod q) ^ 2) * weight w‖ ≤
      B * (((W : ℝ) / q + 1) * (D * q)) := by
    calc
      _ ≤ ∑ w ∈ Finset.Ioc 0 W, ‖g (a * (w : ZMod q) ^ 2) * weight w‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ Finset.Ioc 0 W, B * ‖g (a * (w : ZMod q) ^ 2)‖ := by
        apply Finset.sum_le_sum
        intro w hw'
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hw w hw') (norm_nonneg _)
      _ = B * (∑ w ∈ Finset.Ioc 0 W, ‖g (a * (w : ZMod q) ^ 2)‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ B * (((W : ℝ) / q + 1) * (D * q)) :=
        mul_le_mul_of_nonneg_left (hperiod.trans
          (mul_le_mul_of_nonneg_left hnorm (by positivity))) hB
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)).trans
  have heq : N⁻¹ * (B * (((W : ℝ) / q + 1) * (D * q))) = B * D * (((W : ℝ) + q) / N) := by
    field_simp [hN.ne', hq0.ne']
  rw [heq]
  have hratio : ((W : ℝ) + q) / N ≤ C + 1 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hratio (mul_nonneg hB hD)).trans_eq (by ring)

end Ostmann

end OAI
