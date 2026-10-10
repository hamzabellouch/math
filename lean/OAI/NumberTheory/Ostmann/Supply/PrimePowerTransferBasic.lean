import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingAbel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Finset Set MeasureTheory Ostmann.ZeroDensity
open scoped BigOperators Topology

def smoothPrimeError {q : ℕ} (χ : DirichletCharacter ℂ q) (φ : ℝ → ℝ) (X : ℝ) : ℂ := by
  classical
  exact (∑' n : ℕ, (if n.Prime then (Real.log n : ℂ)*χ n else 0) * (φ ((n : ℝ)/X) : ℂ)) -
    if χ = 1 then ((X * ∫ t in Set.Ioi (0 : ℝ), φ t : ℝ) : ℂ) else 0

theorem smooth_tsum_eq_finite (c : ℕ → ℂ) {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, c n * (φ ((n : ℝ)/X) : ℂ)) =
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, c n * (φ ((n : ℝ)/X) : ℂ) := by
  apply tsum_eq_sum
  intro n hn
  have hz : φ ((n : ℝ)/X) = 0 := by
    by_contra h
    have hi := principal_weight_nonzero_interval hs hX h
    apply hn
    apply Finset.mem_Ioc.mpr
    constructor
    · exact_mod_cast lt_trans (by positivity : (0 : ℝ) < X/2) hi.1
    · exact Nat.le_floor hi.2.le
  simp only [hz, Complex.ofReal_zero, mul_zero]

theorem smoothError_sub_smoothPrimeError {q : ℕ} (χ : DirichletCharacter ℂ q) {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X : ℝ} (hX : 0 < X) :
    smoothError χ φ X - smoothPrimeError χ φ X =
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ)*χ n*(φ ((n : ℝ)/X) : ℂ) := by
  unfold smoothError smoothPrimeError
  rw [smooth_tsum_eq_finite _ hs hX, smooth_tsum_eq_finite _ hs hX,
    sub_sub_sub_cancel_right, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, ite_true, not_true_eq_false, ite_false,
      ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
  · simp only [hp, ite_false, not_false_eq_true, ite_true, zero_mul, sub_zero]

theorem norm_smoothError_sub_smoothPrimeError_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X B : ℝ} (hX : 0 < X)
    (hB : ∀ x, ‖φ x‖ ≤ B) :
    ‖smoothError χ φ X - smoothPrimeError χ φ X‖ ≤ B*(Chebyshev.psi X-Chebyshev.theta X) := by
  rw [smoothError_sub_smoothPrimeError χ hs hX, Chebyshev.psi_sub_theta_eq_sum_not_prime,
    mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hw : |φ ((n : ℝ)/X)| ≤ B := by simpa only [Real.norm_eq_abs] using hB ((n : ℝ)/X)
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n * |φ ((n : ℝ)/X)| :=
      mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)) (abs_nonneg _)
    _ ≤ ArithmeticFunction.vonMangoldt n * B :=
      mul_le_mul_of_nonneg_left hw ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := mul_comm _ _

end Ostmann.Supply

end

end OAI
