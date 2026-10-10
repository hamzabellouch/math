import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The convex hull of the origin and the `d` standard unit vectors. -/
def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))

/-- The first ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def firstBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.castAdd 10 i)

/-- The last ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def secondBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.natAdd 10 i)

/-- The genuine Cartesian product T₁₀ × T₁₀ in Euclidean R²⁰. -/
def productBody : Set (E 20) :=
  {x | firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10}

/-- Compact, convex, and full-dimensional in its specified Euclidean space. -/
def IsConvexBody {d : ℕ} (P : Set (E d)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (interior P).Nonempty

end ProjectionCounterexample

end

end OAI
