import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-!
The explicit twelve-point witness and the ordinary Euclidean Ramsey property.
These definitions contain no proof-specific field derivation or affine-placement assumption.
-/
noncomputable section

namespace GrahamSpherical

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Label := Fin 3 × Fin 4

/-- The factorial series starts at `1!`. -/
def parameter : ℝ := ∑' m : ℕ, 1 / (10 : ℝ) ^ ((m + 1).factorial)

def u : ℝ := (1 - parameter ^ 2) / (1 + parameter ^ 2)
def v : ℝ := (2 * parameter) / (1 + parameter ^ 2)

def squareCoordinate (q : Fin 4) : Fin 2 → ℝ :=
  if q = 0 then ![1, 0] else
  if q = 1 then ![-1, 0] else
  if q = 2 then ![0, 1] else ![0, -1]

/-- First the positively rotated square, then the negatively rotated square,
and finally the original coordinate square. -/
def coordinates (i : Label) : Fin 2 → ℝ :=
  let q := squareCoordinate i.2
  if i.1 = 0 then ![u * q 0 - v * q 1, v * q 0 + u * q 1] else
  if i.1 = 1 then ![u * q 0 + v * q 1, -v * q 0 + u * q 1] else q

def vertex (i : Label) : Point 2 := WithLp.toLp 2 (coordinates i)

def witness : Set (Point 2) := Set.range vertex

def weight (i : Label) : ℤ := if i.1 = 2 then -2 else 1

/-- Arbitrary colorings and exact distance-preserving copies; no measurability,
computability, continuity of the coloring, or extension of the copy is assumed. -/
def AvoidsCopy {d n r : ℕ} (X : Set (Point d)) (color : Point n → Fin r) : Prop :=
  ¬ ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

def EuclideanRamsey {d : ℕ} (X : Set (Point d)) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ n : ℕ, 0 < n ∧
    ∀ color : Point n → Fin r,
      ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

end GrahamSpherical

end

/-! Independent statement of the full authored result. -/
namespace GrahamSpherical.Specification

def FullAuthoredResult : Prop :=
  witness.ncard = 12 ∧
  witness ⊆ Metric.sphere (0 : Point 2) 1 ∧
  (∀ n : ℕ, 0 < n → ∃ color : Point n → Fin 50, AvoidsCopy witness color) ∧
  ¬ EuclideanRamsey witness

end GrahamSpherical.Specification

end OAI
