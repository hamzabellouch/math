import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import OAI.AlgebraicGeometry.StableCoordinate.PrincipalIdeal
import OAI.AlgebraicGeometry.StableCoordinate.AffineNormalization

namespace OAI

/-!
# The coordinate obstruction and rectifiability of every fiber

The ambient algebra automorphisms in this file are arbitrary complex algebra
automorphisms.  In particular, there is no restriction to a chosen subgroup or
triangular form.  The scalar-image characterization keeps the nonzero scalar
which occurs when generators of two equal principal ideals are compared.
-/

namespace StableCoordinate

open MvPolynomial

/-- Rectifiability is equivalent to sending `f` to an affine-linear polynomial
in the first coordinate, with nonzero linear coefficient. -/
theorem rectifiableFiber_iff_affine_image (t : ℂ) :
    IsRectifiableFiber t ↔
      ∃ (φ : R 4 ≃ₐ[ℂ] R 4) (c : ℂ), c ≠ 0 ∧
        φ f = C c * X 0 + C t := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨c, hc, heq⟩ := eq_nonzero_scalar_mul_of_map_span_singleton_eq
      φ.toAlgHom (f := f - C t) (g := X 0) hφ
    refine ⟨φ, c, hc, ?_⟩
    have hC : φ (C t) = C t := φ.commutes t
    change φ (f - C t) = C c * X 0 at heq
    rw [map_sub, hC] at heq
    exact (sub_eq_iff_eq_add).mp heq
  · rintro ⟨φ, c, hc, heq⟩
    use φ
    unfold fiberIdeal
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span ({φ (f - C t)} : Set (R 4)) = Ideal.span {X 0}
    apply span_singleton_eq_of_eq_nonzero_scalar_mul hc
    change φ (f - C t) = C c * X 0
    have hC : φ (C t) = C t := φ.commutes t
    rw [map_sub, hC, heq, add_sub_cancel_right]

/-- For every complex level, rectifiability of the defining hypersurface ideal
is equivalent to the coordinate property of the original polynomial. -/
theorem rectifiableFiber_iff_coordinate (t : ℂ) :
    IsRectifiableFiber t ↔ IsCoordinate (by decide : 0 < 4) f := by
  rw [rectifiableFiber_iff_affine_image]
  constructor
  · rintro ⟨φ, c, hc, hφ⟩
    exact exists_equiv_eq_X_of_affine f 0 c t hc φ hφ
  · rintro ⟨φ, hφ⟩
    refine ⟨φ.trans (affineAll (σ := Fin 4) 1 t one_ne_zero), 1, one_ne_zero, ?_⟩
    change affineAll (σ := Fin 4) 1 t one_ne_zero (φ f) = _
    rw [hφ, affineAll_X]
    rfl

/-- The four-variable coordinate obstruction forbids rectification at every
complex level, with no exclusion of zero or exceptional fibers. -/
theorem noncoordinate_implies_all_fibers_nonrectifiable
    (h : ¬ IsCoordinate (by decide : 0 < 4) f) :
    ∀ t : ℂ, ¬ IsRectifiableFiber t := by
  intro t ht
  exact h ((rectifiableFiber_iff_coordinate t).mp ht)

/-- The all-fiber geometric package follows from actual coordinate-algebra
isomorphisms and the four-variable coordinate obstruction. -/
theorem fiberPackage_of_noncoordinate_of_affine
    (h : ¬ IsCoordinate (by decide : 0 < 4) f)
    (hFibers : ∀ t : ℂ, IsAffineThreeSpaceFiber t) : FiberPackage := by
  intro t
  exact ⟨hFibers t, noncoordinate_implies_all_fibers_nonrectifiable h t⟩

end StableCoordinate

end OAI
