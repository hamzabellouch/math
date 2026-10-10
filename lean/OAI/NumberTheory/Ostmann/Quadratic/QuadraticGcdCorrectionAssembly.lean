import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstCorrectionIdentity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallTotalIdentity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdTransform

namespace OAI

/-! # The original gcd correction consists of the signed first term and the small term -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_corrections_identity (M R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticGcdMomentCorrections M R K D J v =
      (∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ a : quadraticPoissonSigns,
          quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
            (quadraticPoissonSigns_abs a.property) M ((R : ℝ) / D) J R D e K ((e : ℤ) * a) v v) -
        quadraticGcdSmallTotal M J R D K v v := by
  unfold quadraticGcdMomentCorrections quadraticGcdSmallTotal
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [quadratic_first_correction_identity]

theorem quadratic_gcd_corrections_norm (M R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    ‖quadraticGcdMomentCorrections M R K D J v‖ ≤
      (∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns,
        ‖quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
          (quadraticPoissonSigns_abs a.property) M ((R : ℝ) / D) J R D e K ((e : ℤ) * a) v v‖) +
        ‖quadraticGcdSmallTotal M J R D K v v‖ := by
  rw [quadratic_gcd_corrections_identity]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (le_refl _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [norm_mul]
  have he : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_sum_le (Finset.univ : Finset quadraticPoissonSigns) _)

end Ostmann

end OAI
