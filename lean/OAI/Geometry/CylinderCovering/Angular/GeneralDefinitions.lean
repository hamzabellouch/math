import OAI.Geometry.TriangularCovering.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering.AngularGeneral

abbrev Space := TriangularCovering.Space

structure Data where
  count : ℕ
  node : ℕ → ℝ
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  radius : ℕ → ℝ → ℝ

def interval (D : Data) (j : ℕ) : Set ℝ := Icc (D.node j) (D.node (j+1))

def profile (q : ℝ) : ℝ := (q^2+q^4)/16

def lowerDirection (τ : ℝ) (D : Data) (j : ℕ) : Space :=
  TriangularCovering.point 1 (τ*D.alpha j) (τ*D.beta j)

def upperDirection (τ : ℝ) (D : Data) (j : ℕ) : Space :=
  TriangularCovering.point (-τ*D.alpha j) 1 (τ*D.beta j)

def unitDirection (v : Space) : Space := ‖v‖⁻¹ • v

def lowerAxis (τ : ℝ) (D : Data) (j : ℕ) : Space :=
  unitDirection (lowerDirection τ D j)

def upperAxis (τ : ℝ) (D : Data) (j : ℕ) : Space :=
  unitDirection (upperDirection τ D j)

def lowerIntercept (D : Data) (j : ℕ) : Set Space :=
  {z | ∃ q ∈ interval D j, ∃ S ∈ Icc (0:ℝ) (D.radius j q),
    z = TriangularCovering.point 0 (q*S) S}

def upperIntercept (D : Data) (j : ℕ) : Set Space :=
  {z | ∃ q ∈ interval D j, ∃ T ∈ Icc (0:ℝ) (D.radius j q),
    z = TriangularCovering.point (q*T) 0 (1-T)}

def lowerBase (τ : ℝ) (D : Data) (j : ℕ) : Set Space :=
  TriangularCovering.projection (lowerAxis τ D j) '' lowerIntercept D j

def upperBase (τ : ℝ) (D : Data) (j : ℕ) : Set Space :=
  TriangularCovering.projection (upperAxis τ D j) '' upperIntercept D j

def carrier (u : Space) (B : Set Space) : Set Space :=
  {z | ∃ b ∈ B, ∃ r : ℝ, z = b+r • u}

def lowerCylinder (τ : ℝ) (D : Data) (j : ℕ) : Set Space :=
  carrier (lowerAxis τ D j) (lowerBase τ D j)

def upperCylinder (τ : ℝ) (D : Data) (j : ℕ) : Set Space :=
  carrier (upperAxis τ D j) (upperBase τ D j)

def covers (τ : ℝ) (D : Data) : Prop :=
  ∀ z ∈ TriangularCovering.K, ∃ j : Fin D.count,
    z ∈ lowerCylinder τ D j ∨ z ∈ upperCylinder τ D j

def totalArea (τ : ℝ) (D : Data) : ℝ :=
  ∑ j : Fin D.count,
    (TriangularCovering.area (lowerBase τ D j) +
      TriangularCovering.area (upperBase τ D j))

def relativeCost (τ : ℝ) (D : Data) : ℝ :=
  ∑ j : Fin D.count,
    (TriangularCovering.area (lowerBase τ D j) /
      TriangularCovering.shadowArea (lowerAxis τ D j) +
      TriangularCovering.area (upperBase τ D j) /
        TriangularCovering.shadowArea (upperAxis τ D j))

def integralCost (τ : ℝ) (D : Data) : ℝ :=
  ∑ j : Fin D.count, ∫ q in D.node j..D.node (j+1),
    (D.radius j q)^2 / Real.sqrt (1+τ^2*((D.alpha j)^2+2*(D.beta j)^2))

def Admissible (τ η E : ℝ) (D : Data) : Prop :=
  0 < D.count ∧ D.node 0 = -1 ∧ D.node D.count = 1 ∧
  (∀ j < D.count, D.node j < D.node (j+1)) ∧
  (∀ j ≤ D.count, |D.node j| ≤ 1) ∧
  (∃ L : ℝ → ℝ, ContinuousOn L (Icc (-1:ℝ) 1) ∧ L (-1) = 0 ∧ L 1 = 0 ∧
    ∀ j < D.count, ∀ q ∈ interval D j, D.alpha j-q*D.beta j = L q) ∧
  (∀ j < D.count, ContinuousOn (D.radius j) (interval D j)) ∧
  (∀ j < D.count, ∀ q ∈ interval D j, 0 < D.radius j q) ∧
  (∀ j < D.count, ∀ q ∈ interval D j,
    |D.alpha j-(1+q^2)/4| ≤ E*τ^2 ∧
    |D.beta j-q/2| ≤ E*τ^2 ∧
    |D.radius j q-(1/2+τ^2*(profile q+η))| ≤ E*τ^4)

def BaseProperties (u : Space) (B : Set Space) : Prop :=
  ‖u‖ = 1 ∧ (∀ z ∈ B, inner ℝ u z = 0) ∧
  IsCompact B ∧ MeasurableSet B ∧ Measure.euclideanHausdorffMeasure 2 B ≠ ⊤

def IsNondegenerateTriangle (B : Set Space) : Prop :=
  ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧ B = convexHull ℝ (Set.range v)

def Conclusion (τ η A : ℝ) (D : Data) : Prop :=
  covers τ D ∧
  (∀ j < D.count,
    BaseProperties (lowerAxis τ D j) (lowerBase τ D j) ∧
    BaseProperties (upperAxis τ D j) (upperBase τ D j)) ∧
  totalArea τ D / TriangularCovering.H = integralCost τ D ∧
  |totalArea τ D / TriangularCovering.H - (1/2+(2*η-1/240)*τ^2)| ≤ A*τ^4 ∧
  totalArea τ D < TriangularCovering.A_min/2 ∧ relativeCost τ D < 1/2 ∧
  (∀ j < D.count, (∃ r : ℝ, ∀ q ∈ interval D j, D.radius j q = r) →
    IsNondegenerateTriangle (lowerBase τ D j) ∧
    IsNondegenerateTriangle (upperBase τ D j))

def Statement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1/480 → ∀ E : ℝ, 0 ≤ E →
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧
      ∀ τ : ℝ, 0 < τ → τ < δ → ∀ D : Data,
        Admissible τ η E D → Conclusion τ η A D

end CylinderCovering.AngularGeneral

end

end OAI
