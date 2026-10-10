import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

/-- The Hilbert space l²(G)^n, with the product coordinates flattened. -/
abbrev Hilbert (G : Type) (n : ℕ) := lp (fun _ : Fin n × G => ℂ) 2

/-- The identity vector in component i. -/
def identityVector {G : Type} [Group G] {n : ℕ} (i : Fin n) : Hilbert G n :=
  by
    classical
    exact lp.single 2 (i, 1) 1

/-- The unnormalized matrix trace, linear in its operator argument. -/
def groupTrace {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : ℂ :=
  ∑ i : Fin n, inner ℂ (identityVector i) (T (identityVector i))

/-- The invertible-case Fuglede--Kadison determinant.
It is used below only for invertible regular operators. -/
def fkDet {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : ℝ :=
  Real.exp ((groupTrace (CFC.log (star T * T))).re / 2)

/-- Exact coordinate specification of the bounded left-regular operator of A. -/
def IsRegularOperator {G : Type} [Group G] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G))
    (T : Hilbert G n →L[ℂ] Hilbert G n) : Prop :=
  ∀ (ξ : Hilbert G n) (i : Fin n) (h : G),
    (T ξ) (i, h) = ∑ j : Fin n,
      (A i j).coeff.sum fun g z => (z : ℂ) * ξ (j, g⁻¹ * h)

/-- Coefficientwise extension from the integral to the rational group ring. -/
def rationalMatrix {G : Type} [Group G] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    Matrix (Fin n) (Fin n) (MonoidAlgebra ℚ G) :=
  A.map (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ))

/-- An integral group-ring matrix with rational and bounded inverses and determinant in (0, 1). -/
def MainStatement : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Group.FG G) (n : ℕ),
    1 ≤ n ∧ ∃ (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G))
      (T : Hilbert G n →L[ℂ] Hilbert G n),
      IsUnit (rationalMatrix A) ∧ IsRegularOperator A T ∧ IsUnit T ∧
        0 < fkDet T ∧ fkDet T < 1

theorem main : MainStatement := by
  sorry

end GroupRingDeterminant

end

end OAI
