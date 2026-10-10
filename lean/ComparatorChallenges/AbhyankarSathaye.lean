import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

namespace AbhyankarSathaye

/-- In every dimension at least four, a polynomial can define affine space
without being a coordinate of the ambient polynomial ring. -/
theorem exists_noncoordinate_polynomial (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {F}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
        (index : Fin n), equiv (MvPolynomial.X index) = F := by
  sorry

end AbhyankarSathaye

end OAI
