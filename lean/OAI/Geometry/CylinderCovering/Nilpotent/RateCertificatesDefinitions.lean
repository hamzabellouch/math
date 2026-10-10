import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering.NilpotentRate

def UniformSmoothRateStatement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane) (h : ℝ),
    IsCompact D → BoundedSecondNear D G →
    (∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0) →
    ∃ M K C δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ tag : Index → Plane, ∀ Q : Index → Plane ≃ₗᵢ[ℝ] Plane,
      (∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
        IsShearFrame (fderiv ℝ G (tag i)) (Q i)) →
      (∀ i ∈ coarseIndices δ D, ‖fderiv ℝ G (tag i)‖ ≤ M ∧
        ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2) ∧
      (retainedIndices δ (collarRadius M K δ) D Q).Finite ∧
      RuledApproximation.physicalRuled 1 D G 1 ⊆
        constructionCarrier δ (collarRadius M K δ) D G tag Q ∧
      constructionCost h δ (collarRadius M K δ) D G tag Q ≤
        (∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) + C * δ ∧
      constructionCost h δ (collarRadius M K δ) D G tag Q ≤
        (∫ b in D, RuledApproximation.physicalWeight h (G b)) +
          volume.real (gridUnion δ D \ D) + C * δ

def RetainedPhysicalStatement : Prop :=
  ∀ (δ R h : ℝ) (_hδ : 0 < δ) (_hh : 0 < h)
    (D : Set Plane) (G : Plane → Plane) (tag : Index → Plane)
    (Q : Index → Plane ≃ₗᵢ[ℝ] Plane)
    (_hfin : (retainedIndices δ R D Q).Finite) (a : ℝ),
    ∃ n : ℕ, ∃ C₁ C₂ : Fin n → RuledApproximation.Cylinder,
      n = Nat.card (retainedIndices δ R D Q) ∧
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram) ∧
      RuledApproximation.familySet C₁ = RuledApproximation.firstPhysicalMap h ''
        constructionCarrier δ R D G tag Q ∧
      RuledApproximation.familySet C₂ = RuledApproximation.secondPhysicalMap h a ''
        constructionCarrier δ R D G tag Q ∧
      RuledApproximation.familyArea C₁ = h * constructionCost h δ R D G tag Q ∧
      RuledApproximation.familyArea C₂ = h * constructionCost h δ R D G tag Q

structure CompleteSmoothRateStatement : Prop where
  smooth : SmoothRateStatement
  uniform : UniformSmoothRateStatement
  physical : RetainedPhysicalStatement

end CylinderCovering.NilpotentRate

end

end OAI
