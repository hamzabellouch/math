import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.AngularTableGeometry

abbrev Space := TriangularCovering.Space

def dilate (r : ℝ) (S : Set Space) : Set Space := (fun x => r • x) '' S

def body (r : ℝ) : Set Space := dilate r TriangularCovering.K

def lowerBase (r τ : ℝ) (D : AngularGeneral.Data) (j : ℕ) : Set Space :=
  dilate r (AngularGeneral.lowerBase τ D j)

def upperBase (r τ : ℝ) (D : AngularGeneral.Data) (j : ℕ) : Set Space :=
  dilate r (AngularGeneral.upperBase τ D j)

def covers (r τ : ℝ) (D : AngularGeneral.Data) : Prop :=
  ∀ z ∈ body r, ∃ j : Fin D.count,
    z ∈ AngularGeneral.carrier (AngularGeneral.lowerAxis τ D j) (lowerBase r τ D j) ∨
    z ∈ AngularGeneral.carrier (AngularGeneral.upperAxis τ D j) (upperBase r τ D j)

def totalArea (r τ : ℝ) (D : AngularGeneral.Data) : ℝ :=
  ∑ j : Fin D.count,
    (TriangularCovering.area (lowerBase r τ D j) +
      TriangularCovering.area (upperBase r τ D j))

def relativeCost (r τ : ℝ) (D : AngularGeneral.Data) : ℝ :=
  ∑ j : Fin D.count,
    (TriangularCovering.area (lowerBase r τ D j) /
      CylinderCovering.shadowArea (body r) (AngularGeneral.lowerAxis τ D j) +
    TriangularCovering.area (upperBase r τ D j) /
      CylinderCovering.shadowArea (body r) (AngularGeneral.upperAxis τ D j))

def Conclusion (r τ η A : ℝ) (D : AngularGeneral.Data) : Prop :=
  covers r τ D ∧
  (∀ j < D.count,
    AngularGeneral.BaseProperties (AngularGeneral.lowerAxis τ D j) (lowerBase r τ D j) ∧
    AngularGeneral.BaseProperties (AngularGeneral.upperAxis τ D j) (upperBase r τ D j)) ∧
  totalArea r τ D / minimumShadowArea (body r) = AngularGeneral.integralCost τ D ∧
  |totalArea r τ D / minimumShadowArea (body r) - (1/2+(2*η-1/240)*τ^2)| ≤ A*τ^4 ∧
  totalArea r τ D < minimumShadowArea (body r)/2 ∧ relativeCost r τ D < 1/2 ∧
  (∀ j < D.count, (∃ c : ℝ, ∀ q ∈ AngularGeneral.interval D j, D.radius j q = c) →
    AngularGeneral.IsNondegenerateTriangle (lowerBase r τ D j) ∧
    AngularGeneral.IsNondegenerateTriangle (upperBase r τ D j))

end CylinderCovering.AngularTableGeometry

end

end OAI
