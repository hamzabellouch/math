import OAI.Geometry.CylinderCovering.Convexity.NormalFrameDefinitions
import OAI.Geometry.TriangularCovering.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace CylinderBarycentricMetric

abbrev Physical := EuclideanSpace ℝ (Fin 3)
abbrev Barycentric := EuclideanSpace ℝ (Fin 4)

def tetrahedron : Set Barycentric :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i : Fin 4, p i = 1}

def projection (u p : Barycentric) : Barycentric := p - inner ℝ u p • u

def shadowArea (u : Barycentric) : ℝ :=
  (Measure.euclideanHausdorffMeasure 2 (projection u '' tetrahedron)).toReal

def embedding : Physical →ₗ[ℝ] Barycentric where
  toFun z := !₂[z 0 / Real.sqrt 2 - z 2 / 2,
    -z 0 / Real.sqrt 2 - z 2 / 2,
    z 1 / Real.sqrt 2 + z 2 / 2,
    -z 1 / Real.sqrt 2 + z 2 / 2]
  map_add' z w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    ext i
    fin_cases i <;> simp <;> ring

def inverse (p : Barycentric) : Physical :=
  !₂[(p 0 - p 1) / Real.sqrt 2,
     (p 2 - p 3) / Real.sqrt 2,
     p 2 + p 3]

def offset : Barycentric := !₂[1 / 2, 1 / 2, 0, 0]

def fromPhysical (z : Physical) : Barycentric :=
  offset + (1 / Real.sqrt 2) • embedding z

def ProjectionStatement : Prop :=
  (∀ u : Barycentric, ‖u‖ = 1 → (∑ i : Fin 4, u i = 0) →
    shadowArea u = (1 / 2 : ℝ) * ∑ i : Fin 4, |u i|) ∧
  IsLeast {a : ℝ | ∃ u : Barycentric,
    ‖u‖ = 1 ∧ ∑ i : Fin 4, u i = 0 ∧ a = shadowArea u} (1 / Real.sqrt 2)

end CylinderBarycentricMetric

end

end OAI
