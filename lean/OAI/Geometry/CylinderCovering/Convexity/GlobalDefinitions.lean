import OAI.Geometry.CylinderCovering.Angular.ConstructionDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering

abbrev Space := EuclideanSpace ℝ (Fin 3)

def IsRegularTetrahedron (K : Set Space) : Prop :=
  ∃ v : Fin 4 → Space, AffineIndependent ℝ v ∧
    ∃ edge : ℝ, 0 < edge ∧
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) ∧
      K = convexHull ℝ (range v)

def shadowArea (K : Set Space) (u : Space) : ℝ :=
  TriangularCovering.area (TriangularCovering.projection u '' K)

def minimumShadowArea (K : Set Space) : ℝ :=
  sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea K u}

def triangularCovers {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) : Prop :=
  ∀ x ∈ K, ∃ i : Fin n, x ∈ (C i).carrier

def triangularRelativeCost {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) : ℝ :=
  ∑ i, TriangularCovering.area (C i).base / shadowArea K (C i).axis

def relativeCost {n : ℕ} (K : Set Space)
    (C : Fin n → RuledApproximation.Cylinder) : ℝ :=
  ∑ i, (C i).area / shadowArea K (C i).axis

def AngularExplicitStatement : Prop :=
  TriangularCovering.AngularAreaStatement ∧ TriangularCovering.ExplicitAngularStatement

def RegularTriangularCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → TriangularCovering.TriCylinder,
      triangularCovers K C ∧
      TriangularCovering.totalArea C < minimumShadowArea K / 2 ∧
      triangularRelativeCost K C < 1 / 2

def RegularParallelogramCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, (C i).parallelogram) ∧
      K ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧
      relativeCost K C < 1 / 2

def RegularOpenCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, (C i).openBounded) ∧
      K ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧
      relativeCost K C < 1 / 2

end CylinderCovering

end

end OAI
