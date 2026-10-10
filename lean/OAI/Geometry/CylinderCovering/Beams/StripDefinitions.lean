import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering.BeamStrip

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def vec (x y z : ℝ) : Space := !₂[x, y, z]

def vertical : Space := vec 0 0 1

def denominator (q : ℝ) : ℝ := Real.sqrt (2 * (1 + q ^ 2))

def normal (q : ℝ) : Space :=
  vec ((1 + q) / denominator q) ((1 - q) / denominator q) 0

def axis (q : ℝ) : Space :=
  vec ((1 - q) / denominator q) (-(1 + q) / denominator q) 0

def rectangle (q A l r : ℝ) : Set Space :=
  {z | ∃ s ∈ Icc (-A) A, ∃ t ∈ Icc l r, z = s • normal q + t • vertical}

def cylinder (q A l r : ℝ) : Set Space :=
  {z | ∃ b ∈ rectangle q A l r, ∃ s : ℝ, z = b + s • axis q}

def area (S : Set Space) : ℝ := (Measure.euclideanHausdorffMeasure 2 S).toReal

def strip (β M a b : ℝ) (W q : ℝ → ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, z = vec (β*x) (β*y) t ∧ t ∈ Icc a b ∧
    |x| ≤ M ∧ |y| ≤ M ∧ |(1+q t)*x+(1-q t)*y| ≤ W t}

def IsHorizontalRectangle (C : RuledApproximation.Cylinder) : Prop :=
  ∃ q A l r : ℝ, 0 < A ∧ l < r ∧ C.axis = axis q ∧
    ((fun z : ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) => (z : Space)) '' C.base) = rectangle q A l r

def IsRectangle (B : Set Space) : Prop :=
  ∃ c u v : Space, inner ℝ u v = 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
    B = {z | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      z = c + s • u + t • v}

def HasRectangularBase (C : RuledApproximation.Cylinder) : Prop :=
  IsRectangle ((fun z : ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) =>
    (z : Space)) '' C.base)

end CylinderCovering.BeamStrip

end

end OAI
