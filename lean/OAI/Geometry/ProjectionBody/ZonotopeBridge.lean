import OAI.Geometry.ProjectionBody.Definitions
import OAI.Geometry.ProjectionBody.UnitSupport
import OAI.Geometry.Zonotope.Euclidean

namespace OAI

/-!
Generic bridge from a *proved* directional projection-volume formula to the
explicit zonotope. The brightness formula is an explicit hypothesis of these
helper lemmas; no final counterexample theorem assumes it.
-/
noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- A unit-direction brightness formula identifies the actual projection body. -/
theorem projectionBody_eq_zonotope {d : ℕ} (P : Set (E d)) (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E d, ‖u‖ = 1 →
      projectionVolume P u = c * DiagonalZonotope.support (WithLp.ofLp u)) :
    projectionBody P = DiagonalZonotope.euclidean c := by
  calc
    projectionBody P = {x : E d | ∀ u : E d, ‖u‖ = 1 →
        ⟪u, x⟫ ≤ c * DiagonalZonotope.support (WithLp.ofLp u)} := by
      ext x
      constructor
      · intro hx u hu
        rw [← hbrightness u hu]
        exact hx u hu
      · intro hx u hu
        rw [hbrightness u hu]
        exact hx u hu
    _ = {x : E d | ∀ u : E d,
        ⟪u, x⟫ ≤ c * DiagonalZonotope.support (WithLp.ofLp u)} := by
      apply unit_support_halfspaces_eq
      · simp [DiagonalZonotope.support]
      · intro a ha u
        change c * DiagonalZonotope.support (a • WithLp.ofLp u) = _
        rw [DiagonalZonotope.support_smul, abs_of_nonneg ha]
        ring
    _ = DiagonalZonotope.euclidean c :=
      (DiagonalZonotope.euclidean_eq_halfspaces c hc).symm

/-- The brightness hypothesis gives both a genuine body and support attainment. -/
theorem projection_zonotope_is_body_and_attains {d : ℕ} (P : Set (E d))
    (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E d, ‖u‖ = 1 →
      projectionVolume P u = c * DiagonalZonotope.support (WithLp.ofLp u)) :
    IsConvexBody (projectionBody P) ∧
      ∀ u : E d, ‖u‖ = 1 → ∃ x ∈ projectionBody P, ⟪u, x⟫ = projectionVolume P u := by
  have hbody := projectionBody_eq_zonotope P c hc hbrightness
  constructor
  · rw [hbody]
    exact ⟨DiagonalZonotope.isCompact_euclidean c,
      DiagonalZonotope.convex_euclidean c,
      DiagonalZonotope.euclidean_interior_nonempty c hc.ne'⟩
  · intro u hu
    obtain ⟨x, hx, heq⟩ := DiagonalZonotope.euclidean_support_attained c u
    refine ⟨x, hbody.symm ▸ hx, ?_⟩
    rw [hbrightness u hu]
    exact heq

end ProjectionCounterexample

end

end OAI
