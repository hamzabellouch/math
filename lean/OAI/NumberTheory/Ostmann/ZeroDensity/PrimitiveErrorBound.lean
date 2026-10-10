import OAI.NumberTheory.Ostmann.ZeroDensity.OccurrenceSum
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveErrorSum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem totalPrimitiveError_le_of_explicit_bounds (Q : ℕ) (hQ : 0 < Q)
    (φ : ℝ → ℝ) (X T : ℝ) {A R E : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hprincipal : ‖smoothError (1 : DirichletCharacter ℂ 1) φ X‖ ≤ E)
    (hcharacters : ∀ χ : NonprincipalPrimitiveFamily Q,
      ‖smoothError χ.val.2.val φ X‖ ≤ A*
        ((∑ ρ ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset.filter
            (fun ρ => (1 : ℝ)/2 ≤ ρ.re),
          (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ : ℝ)*X^ρ.re)+R)) :
    totalPrimitiveError Q none φ X ≤
      E+A*((∑ z ∈ retainedZeros Q none (1/2) T, X^z.point.re)+(Q : ℝ)^2*R) := by
  classical
  let Z : NonprincipalPrimitiveFamily Q → ℝ := fun χ =>
    ∑ ρ ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset.filter
      (fun ρ => (1 : ℝ)/2 ≤ ρ.re),
        (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ : ℝ)*X^ρ.re
  have hzero : (∑ χ : NonprincipalPrimitiveFamily Q, Z χ) =
      ∑ z ∈ retainedZeros Q none (1/2) T, X^z.point.re := by
    have hz := sum_retainedZeros Q none ((1 : ℝ)/2) T
      (fun (_χ : NonprincipalPrimitiveFamily Q) (ρ : ℂ) => X^ρ.re)
    simpa only [Z, Finset.sum_filter, ne_eq, reduceCtorEq, not_false_eq_true, true_and, nsmul_eq_mul] using hz.symm
  have hcard : (Fintype.card (NonprincipalPrimitiveFamily Q) : ℝ) ≤ (Q : ℝ)^2 := by
    exact_mod_cast card_nonprincipalPrimitiveFamily_le Q
  rw [totalPrimitiveError_split Q hQ]
  apply add_le_add hprincipal
  calc
    (∑ χ : NonprincipalPrimitiveFamily Q, ‖smoothError χ.val.2.val φ X‖) ≤
        ∑ χ : NonprincipalPrimitiveFamily Q, A*(Z χ+R) :=
      Finset.sum_le_sum (fun χ _ => hcharacters χ)
    _ = A*((∑ χ : NonprincipalPrimitiveFamily Q, Z χ)+
        (Fintype.card (NonprincipalPrimitiveFamily Q) : ℝ)*R) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    _ = A*((∑ z ∈ retainedZeros Q none (1/2) T, X^z.point.re)+
        (Fintype.card (NonprincipalPrimitiveFamily Q) : ℝ)*R) := by rw [hzero]
    _ ≤ A*((∑ z ∈ retainedZeros Q none (1/2) T, X^z.point.re)+(Q : ℝ)^2*R) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hR)) hA

end Ostmann.ZeroDensity

end

end OAI
