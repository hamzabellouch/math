import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Caps.CapsDefinitions

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.HalfheightCertificates
abbrev Space := TriangularCovering.Space

def IsTrapezoid (B : Set Space) : Prop :=
  ∃ v : Fin 4 → Space,
    B = convexHull ℝ (range v) ∧ Function.Injective v ∧
    AffineIndependent ℝ ![v 0,v 1,v 2] ∧
    ∃ d : Space, ∃ a b : ℝ, d ≠ 0 ∧ 0 < a ∧ 0 < b ∧
      v 1-v 0 = a • d ∧ v 3-v 2 = b • d

def ShapeStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ R : ℝ → ℝ,
    ContinuousOn R (Icc (-1) 1) → (∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ R r) →
    ∀ N : ℕ, ∀ i : Fin N,
      IsTrapezoid (HalfheightFinite.firstBase δ R N i) ∧
      IsTrapezoid (HalfheightFinite.secondBase δ R N i)

open HalfHeightCaps

def QuantitativeStatement : Prop :=
  (∀ δ X Y Z r s u v : ℝ,
    0 ≤ δ → δ ≤ 1/2 → |X| ≤ 1 → |Y| ≤ 1 → |r| ≤ 1 → |s| ≤ 1 →
    1/2 ≤ u → 1/2 ≤ v →
    Y = u*r+δ*X*alpha r → Z = u+δ*X*beta r →
    X = v*s-δ*Y*alpha s → 1-Z = v-δ*Y*beta s →
    (1/2 ≤ 1-δ*X*r ∧ 1/2 ≤ 1+δ*Y*s) ∧
    (0 ≤ u-1/2 ∧ u-1/2 ≤ 2*δ^2 ∧ 0 ≤ v-1/2 ∧ v-1/2 ≤ 2*δ^2) ∧
    (|Y-r/2| ≤ 3*δ/2 ∧ |X-s/2| ≤ 3*δ/2) ∧
    (X^2*alpha r+Y^2*alpha s ≤ (s^2*alpha r+r^2*alpha s)/4+9*δ/4 ∧
      X^2*alpha r+Y^2*alpha s ≤ F r+F s+9*δ/4)) ∧
  (∀ δ r s : ℝ, 0 ≤ δ → δ ≤ 1/2 → |r| ≤ 1 → |s| ≤ 1 →
    F r+F s+15*δ/4 ≤ (1-δ)*(F r+F s+8*δ)) ∧
  (∀ δ X Y Z r s u v : ℝ,
    0 < δ → δ ≤ 1/2 → |X| ≤ 1 → |Y| ≤ 1 → |r| ≤ 1 → |s| ≤ 1 →
    Y = u*r+δ*X*alpha r → Z = u+δ*X*beta r →
    X = v*s-δ*Y*alpha s → 1-Z = v-δ*Y*beta s →
    ¬ (cubicCap δ r < u ∧ cubicCap δ s < v))

def Statement : Prop := ShapeStatement ∧ QuantitativeStatement

end CylinderCovering.HalfheightCertificates

end

end OAI
