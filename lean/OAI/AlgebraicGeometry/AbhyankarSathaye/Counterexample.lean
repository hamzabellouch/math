import OAI.AlgebraicGeometry.AbhyankarSathaye.FiberFormulas
import OAI.AlgebraicGeometry.AbhyankarSathaye.LinearPresentation
import OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization

namespace OAI

/-!
# A polynomial hypersurface with a non-coordinate equation

The explicit polynomial `F` has zero fiber isomorphic to affine three-space,
but has a critical point on the fiber of value `-1`, obstructing its being a
polynomial coordinate. Both conclusions persist after adjoining any number
of unused variables.
-/

namespace AbhyankarSathaye

/-- The explicit hypersurface has a polynomial coordinate ring but its defining
polynomial is not a coordinate, in every ambient dimension at least four. -/
theorem counterexample :
    Nonempty ((R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ) ∧
    (∀ index : Fin 4, MvPolynomial.eval criticalPoint (MvPolynomial.pderiv index F) = 0) ∧
    MvPolynomial.eval criticalPoint F = -1 ∧
    (¬ ∃ (equiv : R ≃ₐ[ℂ] R) (index : Fin 4), equiv (MvPolynomial.X index) = F) ∧
    ∀ (dimension : ℕ) (bound : 4 ≤ dimension),
      Nonempty ((MvPolynomial (Fin dimension) ℂ ⧸ Ideal.span {extendedF bound}) ≃ₐ[ℂ]
        MvPolynomial (Fin (dimension - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin dimension) ℂ ≃ₐ[ℂ] MvPolynomial (Fin dimension) ℂ)
        (index : Fin dimension), equiv (MvPolynomial.X index) = extendedF bound :=
  ⟨⟨fiberEquiv⟩, critical_derivatives, eval_F, F_not_coordinate,
    fun _ bound => ⟨⟨extendedFiberEquiv bound⟩, extendedF_not_coordinate bound⟩⟩

/-- In every dimension at least four, a polynomial can define affine space
without being a coordinate of the ambient polynomial ring. -/
theorem exists_noncoordinate_polynomial (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {F}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
        (index : Fin n), equiv (MvPolynomial.X index) = F :=
  ⟨extendedF hn, counterexample.2.2.2.2 n hn⟩

end AbhyankarSathaye

end OAI
