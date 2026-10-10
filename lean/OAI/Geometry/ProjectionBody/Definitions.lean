import OAI.Geometry.ProjectionBody.GeometryDefinitions
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure

namespace OAI

/-!
Geometric definitions for the product counterexample.
The projection measure is the canonically normalized Euclidean Hausdorff
measure of dimension `d - 1`, not ambient `d`-dimensional measure.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- Orthogonal projection onto the hyperplane normal to `u`. -/
def project {d : ℕ} (u : E d) : E d →L[ℝ] E d :=
  (ℝ ∙ u)ᗮ.starProjection

/-- Actual (d−1)-dimensional Euclidean volume of the orthogonal projection. -/
def projectionVolume {d : ℕ} (P : Set (E d)) (u : E d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1) (project u '' P)).toReal

/-- The projection body, defined entirely by its directional projection volumes.
The bounds are the normalized Hausdorff measures of orthogonal projections. -/
def projectionBody {d : ℕ} (P : Set (E d)) : Set (E d) :=
  {x | ∀ u : E d, ‖u‖ = 1 → ⟪u, x⟫ ≤ projectionVolume P u}

/-- Lebesgue volume in the ambient Euclidean space. -/
def bodyVolume {d : ℕ} (P : Set (E d)) : ℝ := (volume P).toReal

/-- The normalized projection-body volume. -/
def ratio {d : ℕ} (P : Set (E d)) : ℝ :=
  bodyVolume (projectionBody P) / bodyVolume P ^ (d - 1)

end ProjectionCounterexample

end

end OAI
