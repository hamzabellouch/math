import Mathlib

namespace OAI

noncomputable section

namespace ComplexCancellation

abbrev P := MvPolynomial (Fin 5) ℂ

def p : P := MvPolynomial.X 0
def s : P := MvPolynomial.X 1
def u : P := MvPolynomial.X 2
def F : P := MvPolynomial.X 3
def J : P := MvPolynomial.X 4
def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F
def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u
abbrev A := P ⧸ Ideal.span {H}

def MainStatement : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ ringKrullDim A = 4 ∧
  Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
  ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ)

theorem main : MainStatement := by
  sorry

end ComplexCancellation

end

end OAI
