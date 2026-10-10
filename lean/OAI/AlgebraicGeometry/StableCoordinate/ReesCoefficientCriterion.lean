import OAI.AlgebraicGeometry.StableCoordinate.FilteredRees

namespace OAI

/-!
# Coefficientwise vanishing in an associated graded algebra

The principal Rees ideal `(T)` consists precisely of Laurent polynomials whose
coefficient in degree `d` belongs to `F (d-1)`.  This gives an actual
coefficientwise kernel test for the Rees model, including negative degrees.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

/-- The complete defining-ideal membership criterion for the Rees special fiber. -/
theorem mem_parameterIdeal_iff (hmono : Monotone F) (p : rees F) :
    p ∈ parameterIdeal F hmono ↔
      ∀ d : ℤ, (p : LaurentPolynomial A).coeff d ∈ F (d - 1) := by
  rw [parameterIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩ d
    have he := congrArg (fun p : rees F => (p : LaurentPolynomial A).coeff d) hq
    have hae : (p : LaurentPolynomial A).coeff d =
        (q : LaurentPolynomial A).coeff (d - 1) := by
      change (p : LaurentPolynomial A).coeff d =
        (AddMonoidAlgebra.single 1 1 * (q : LaurentPolynomial A)).coeff d at he
      rw [AddMonoidAlgebra.coeff_single_mul_apply] at he
      simpa only [one_mul, sub_eq_add_neg, add_comm] using he
    rw [hae]
    exact q.property (d - 1)
  · intro hp
    let q : rees F := ⟨AddMonoidAlgebra.single (-1) 1 * (p : LaurentPolynomial A), by
      intro d
      rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      have hd := hp (1 + d)
      simpa only [neg_neg, show (1 : ℤ) + d - 1 = d by omega] using hd⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change (p : LaurentPolynomial A) = AddMonoidAlgebra.single 1 1 *
      (AddMonoidAlgebra.single (-1) 1 * (p : LaurentPolynomial A))
    rw [← mul_assoc, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, mul_one, ← AddMonoidAlgebra.one_def, one_mul]

/-- A Rees representative vanishes in the associated graded algebra iff each
coefficient has dropped one filtration step. -/
theorem quotient_mk_eq_zero_iff (hmono : Monotone F) (p : rees F) :
    Ideal.Quotient.mk (parameterIdeal F hmono) p = 0 ↔
      ∀ d : ℤ, (p : LaurentPolynomial A).coeff d ∈ F (d - 1) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_parameterIdeal_iff]

/-- Two arbitrary Rees representatives determine the same graded element iff
their coefficientwise difference lies one step lower. -/
theorem quotient_mk_eq_iff (hmono : Monotone F) (p q : rees F) :
    Ideal.Quotient.mk (parameterIdeal F hmono) p =
        Ideal.Quotient.mk (parameterIdeal F hmono) q ↔
      ∀ d : ℤ, (p : LaurentPolynomial A).coeff d - (q : LaurentPolynomial A).coeff d ∈
        F (d - 1) := by
  rw [← sub_eq_zero, ← map_sub, quotient_mk_eq_zero_iff]
  rfl

end StableCoordinate.FilteredRees

end OAI
