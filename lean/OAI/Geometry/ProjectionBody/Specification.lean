import OAI.Geometry.ProjectionBody.Counterexample

namespace OAI

open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample.Specification

theorem product_is_convex_body : IsConvexBody productBody := productBody_convexBody

theorem projection_support_attained :
    ∀ P : Set (E 20), P = simplex 20 ∨ P = productBody →
      IsConvexBody (projectionBody P) ∧
      ∀ u : E 20, ‖u‖ = 1 →
        ∃ x ∈ projectionBody P, ⟪u, x⟫ = projectionVolume P u := by
  intro P hP
  rcases hP with rfl | rfl
  · exact simplex_twenty_projection_support
  · exact product_projection_support

theorem simplex_ratio :
    ratio (simplex 20) = ((21 : ℝ) * (20 : ℝ) ^ 20) / (Nat.factorial 20 : ℝ) :=
  simplex_twenty_ratio

theorem product_ratio :
    ratio productBody / ratio (simplex 20) = (22355476 : ℝ) / 22020096 ∧
      (1 : ℝ) < ratio productBody / ratio (simplex 20) := by
  constructor
  · exact product_to_simplex_ratio
  · rw [product_to_simplex_ratio]
    exact numerical_strict_excess

theorem simplex_upper_bound_false :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) :=
  universal_simplex_upper_bound_false

end ProjectionCounterexample.Specification

end OAI
