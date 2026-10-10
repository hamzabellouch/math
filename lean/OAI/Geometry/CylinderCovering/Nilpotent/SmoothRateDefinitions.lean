import OAI.Geometry.RuledCovering.Model
import OAI.Geometry.CylinderCovering.Nilpotent.GridDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace CylinderCovering.NilpotentRate

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Index := ℤ × ℤ

def integerVector (i : Index) : Plane := RuledApproximation.vec2 i.1 i.2

def tile (Q : Plane ≃ₗᵢ[ℝ] Plane) (τ : ℝ) (i : Index) : Set Plane :=
  (fun z => τ • Q (integerVector i + z)) '' RuledApproximation.unitSquare

def cell (δ : ℝ) (i : Index) : Set Plane := NilpotentGrid.coarseCell δ i

def coarseIndices (δ : ℝ) (D : Set Plane) : Set Index :=
  {i | (cell δ i ∩ D).Nonempty}

def gridUnion (δ : ℝ) (D : Set Plane) : Set Plane :=
  ⋃ i ∈ coarseIndices δ D, cell δ i

def fineCenter (δ : ℝ) (Q : Plane ≃ₗᵢ[ℝ] Plane) (j : Index) : Plane :=
  δ ^ 2 • Q (integerVector j)

def collarRadius (M K δ : ℝ) : ℝ := (1 + M) * (Real.sqrt 2 + K) * δ ^ 2

def retainedIndices (δ R : ℝ) (D : Set Plane) (Q : Index → Plane ≃ₗᵢ[ℝ] Plane) :
    Set (Index × Index) :=
  {ij | ij.1 ∈ coarseIndices δ D ∧
    Metric.infDist (fineCenter δ (Q ij.1) ij.2) (cell δ ij.1) ≤ R}

def affineVelocity (G : Plane → Plane) (tag : Index → Plane) (i : Index) (l : Plane) : Plane :=
  G (tag i) + fderiv ℝ G (tag i) (l - tag i)

def constructionCost (h δ R : ℝ) (D : Set Plane) (G : Plane → Plane)
    (tag : Index → Plane) (Q : Index → Plane ≃ₗᵢ[ℝ] Plane) : ℝ :=
  ∑' ij : retainedIndices δ R D Q,
    volume.real (tile (Q ij.val.1) (δ ^ 2) ij.val.2) *
      RuledApproximation.physicalWeight h
        (affineVelocity G tag ij.val.1 (fineCenter δ (Q ij.val.1) ij.val.2))

def constructionCarrier (δ R : ℝ) (D : Set Plane) (G : Plane → Plane)
    (tag : Index → Plane) (Q : Index → Plane ≃ₗᵢ[ℝ] Plane) : Set RuledApproximation.Space :=
  ⋃ ij ∈ retainedIndices δ R D Q,
    RuledApproximation.auxiliaryCylinder (tile (Q ij.1) (δ ^ 2) ij.2)
      (affineVelocity G tag ij.1 (fineCenter δ (Q ij.1) ij.2))

def IsShearFrame (A : Plane →L[ℝ] Plane) (Q : Plane ≃ₗᵢ[ℝ] Plane) : Prop :=
  ∃ d : ℝ, ∀ z : Plane, Q.symm (A (Q z)) = RuledApproximation.vec2 (d * z 1) 0

def BoundedSecondNear (D : Set Plane) (G : Plane → Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 1 G U ∧
    (∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ G) x) ∧
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ H

def SmoothRateStatement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane) (h : ℝ),
    IsCompact D → BoundedSecondNear D G →
    (∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0) → 0 < h →
    (Tendsto (fun δ : ℝ => volume.real (gridUnion δ D \ D)) (𝓝[>] 0) (𝓝 0)) ∧
    ∃ M K C δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ tag : Index → Plane, ∃ Q : Index → Plane ≃ₗᵢ[ℝ] Plane,
        (∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
          IsShearFrame (fderiv ℝ G (tag i)) (Q i) ∧ ‖fderiv ℝ G (tag i)‖ ≤ M ∧
          ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2) ∧
        (retainedIndices δ (collarRadius M K δ) D Q).Finite ∧
        RuledApproximation.physicalRuled 1 D G 1 ⊆
          constructionCarrier δ (collarRadius M K δ) D G tag Q ∧
        constructionCost h δ (collarRadius M K δ) D G tag Q ≤
          (∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) + C * δ ∧
        constructionCost h δ (collarRadius M K δ) D G tag Q ≤
          (∫ b in D, RuledApproximation.physicalWeight h (G b)) +
            volume.real (gridUnion δ D \ D) + C * δ

end CylinderCovering.NilpotentRate

end

end OAI
