import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))

def IsConvexBody {d : ℕ} (P : Set (E d)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (interior P).Nonempty

def project {d : ℕ} (u : E d) : E d →L[ℝ] E d :=
  (ℝ ∙ u)ᗮ.starProjection

def projectionVolume {d : ℕ} (P : Set (E d)) (u : E d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1) (project u '' P)).toReal

def projectionBody {d : ℕ} (P : Set (E d)) : Set (E d) :=
  {x | ∀ u : E d, ‖u‖ = 1 → ⟪u, x⟫ ≤ projectionVolume P u}

def bodyVolume {d : ℕ} (P : Set (E d)) : ℝ := (volume P).toReal

def ratio {d : ℕ} (P : Set (E d)) : ℝ :=
  bodyVolume (projectionBody P) / bodyVolume P ^ (d - 1)

theorem universal_simplex_upper_bound_false :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) := by
  sorry

end ProjectionCounterexample

end

end OAI
