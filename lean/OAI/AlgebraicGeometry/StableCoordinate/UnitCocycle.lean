import Mathlib.Algebra.MvPolynomial.Nilpotent

namespace OAI

/-!
# Rigidity of polynomial units and normalized cocycles

The source's line-bundle action lift compares two maps by a unit in `R[T,S]`.
For a reduced coefficient ring, such a unit cannot depend on either parameter.
This file supplies precisely that algebraic step.  It does not assert the
existence of line-bundle trivializations, a lift, or a locally nilpotent derivation.

Source: `sources/build/source/sections/04-bundle.tex`, `bun:homotopy` and
`bun:action-lift`, especially the normalized group-law comparison.
-/

namespace StableCoordinate

open MvPolynomial

section PolynomialUnits

variable {σ R : Type*} [CommRing R] [IsReduced R]

/-- A polynomial unit over a reduced ring is the constant polynomial given by
any specialization of its parameters.  In particular this applies to an
integral coordinate ring or any of its localizations. -/
theorem polynomial_unit_eq_C_eval {p : MvPolynomial σ R} (hp : IsUnit p)
    (x : σ → R) : p = C (eval x p) := by
  obtain ⟨r, _, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp hp
  simp

/-- Polynomial units do not depend on the value of the polynomial parameters. -/
theorem polynomial_unit_eval_independent {p : MvPolynomial σ R} (hp : IsUnit p)
    (x y : σ → R) : eval x p = eval y p := by
  obtain ⟨r, _, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp hp
  simp

/-- Two polynomial units agreeing at one parameter value agree everywhere. -/
theorem polynomial_units_eq_of_eval_eq {p q : MvPolynomial σ R}
    (hp : IsUnit p) (hq : IsUnit q) (x : σ → R)
    (h : eval x p = eval x q) : p = q := by
  rw [polynomial_unit_eq_C_eval hp x, polynomial_unit_eq_C_eval hq x, h]

/-- A polynomial unit normalized to one at one parameter value is identically one. -/
theorem polynomial_unit_eq_one_of_eval_eq_one {p : MvPolynomial σ R}
    (hp : IsUnit p) (x : σ → R) (h : eval x p = 1) : p = 1 := by
  rw [polynomial_unit_eq_C_eval hp x, h, map_one]

/-- Evaluation at a point identifies polynomial units with coefficient-ring units. -/
noncomputable def polynomialUnitsEquiv (x : σ → R) : (MvPolynomial σ R)ˣ ≃* Rˣ where
  toFun := Units.map (eval x).toMonoidHom
  invFun := Units.map C.toMonoidHom
  left_inv u := by
    apply Units.ext
    exact (polynomial_unit_eq_C_eval u.isUnit x).symm
  right_inv u := by
    ext
    simp
  map_mul' u v := by
    simp

/-- The normalization step used for the ratio of the two possible group-law
composites in the lifted additive action.  The two independent parameters are
represented by `Fin 2`; both are specialized to zero. -/
theorem normalized_two_parameter_unit_eq_one
    {c : MvPolynomial (Fin 2) R} (hc : IsUnit c)
    (hzero : eval (fun _ => 0) c = 1) : c = 1 :=
  polynomial_unit_eq_one_of_eval_eq_one hc (fun _ => 0) hzero

end PolynomialUnits

end StableCoordinate

end OAI
