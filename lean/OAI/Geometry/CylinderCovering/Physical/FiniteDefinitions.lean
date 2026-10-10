import OAI.Geometry.CylinderCovering.Physical.CoordinatesDefinitions
import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions

namespace OAI

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RadialPhysical

def axialBound (centered : Bool) (b : ℝ) : ℝ := if centered then 2*b else b

def modelBody (centered : Bool) (b : ℝ) : Set Space :=
  if centered then
    {z | ∃ x y t : ℝ, |x| ≤ b*(1+t) ∧ |y| ≤ b*(1-t) ∧ z = point b x y t}
  else tetrahedron b

def upperPoint (b eta rho s x : ℝ) : Space :=
  point b x (rho*s-eta*x*(s^2+b^2)/2) (1-rho+eta*x*s)

def lowerPoint (centered : Bool) (b eta rho s y : ℝ) : Space :=
  point b (rho*s+eta*y*(s^2+b^2)/2) y
    ((if centered then (-1:ℝ) else 0)+rho+eta*y*s)

def upperSweepOn (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ) (I : Set ℝ) : Set Space :=
  {z | ∃ s ∈ I, ∃ rho ∈ Icc (0:ℝ) (T s), ∃ x : ℝ,
    |x| ≤ axialBound centered b ∧ z = upperPoint b eta rho s x}

def lowerSweepOn (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ) (I : Set ℝ) : Set Space :=
  {z | ∃ s ∈ I, ∃ rho ∈ Icc (0:ℝ) (T s), ∃ y : ℝ,
    |y| ≤ axialBound centered b ∧ z = lowerPoint centered b eta rho s y}

def upperPhysicalAxis (b eta s : ℝ) : Space :=
  let v := point b 1 (-eta*(s^2+b^2)/2) (eta*s)
  ‖v‖⁻¹ • v

def lowerPhysicalAxis (b eta s : ℝ) : Space :=
  let v := point b (eta*(s^2+b^2)/2) 1 (eta*s)
  ‖v‖⁻¹ • v

def upperPhysicalBase (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (upperPhysicalAxis b eta (tag i)) ''
    upperSweepOn centered b eta T (CylinderCovering.RadialRiemann.cell (-b) b N i)

def lowerPhysicalBase (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (lowerPhysicalAxis b eta (tag i)) ''
    lowerSweepOn centered b eta T (CylinderCovering.RadialRiemann.cell (-b) b N i)

def physicalActualCost (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area (upperPhysicalBase centered b eta T N tagU i)) +
  (∑ i : Fin N, TriangularCovering.area (lowerPhysicalBase centered b eta T N tagL i))

def physicalBaseProperties (u : Space) (B : Set Space) : Prop :=
  ‖u‖ = 1 ∧ IsCompact B ∧ MeasurableSet B ∧
    Measure.euclideanHausdorffMeasure 2 B ≠ ⊤ ∧ (∀ z ∈ B, inner ℝ u z = 0)

def PhysicalFiniteStatement : Prop :=
  ∀ (centered : Bool) (b eta : ℝ), 0 < b → ∀ T : ℝ → ℝ,
    ContinuousOn T (Icc (-b) b) → (∀ s ∈ Icc (-b) b, 0 ≤ T s) →
    ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagU N)) →
    (∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagL N)) →
    ∃ U L : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i, (U N i).axis = upperPhysicalAxis b eta (tagU N i) ∧
          (L N i).axis = lowerPhysicalAxis b eta (tagL N i) ∧
          upperPhysicalBase centered b eta T N (tagU N) i ⊆ (U N i).base ∧
          lowerPhysicalBase centered b eta T N (tagL N) i ⊆ (L N i).base ∧
          physicalBaseProperties (upperPhysicalAxis b eta (tagU N i))
            (upperPhysicalBase centered b eta T N (tagU N) i) ∧
          physicalBaseProperties (lowerPhysicalAxis b eta (tagL N i))
            (lowerPhysicalBase centered b eta T N (tagL N) i)) ∧
        (∀ z ∈ upperSweepOn centered b eta T (Icc (-b) b),
          (∃ i : Fin N, z ∈ (U N i).carrier) ∧
          (∃ i : Fin N, z ∈ CylinderCovering.RadialSweep.cylinder
            (upperPhysicalAxis b eta (tagU N i))
            (upperPhysicalBase centered b eta T N (tagU N) i))) ∧
        (∀ z ∈ lowerSweepOn centered b eta T (Icc (-b) b),
          (∃ i : Fin N, z ∈ (L N i).carrier) ∧
          (∃ i : Fin N, z ∈ CylinderCovering.RadialSweep.cylinder
            (lowerPhysicalAxis b eta (tagL N i))
            (lowerPhysicalBase centered b eta T N (tagL N) i)))) ∧
      Tendsto (fun N => TriangularCovering.totalArea (U N) +
        TriangularCovering.totalArea (L N)) atTop (𝓝 (scaledCost b eta T)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
        physicalActualCost centered b eta T N (tagU N) (tagL N) ≤ scaledCost b eta T + δ) ∧
      Filter.limsup (fun N => physicalActualCost centered b eta T N (tagU N) (tagL N))
        atTop ≤ scaledCost b eta T

end RadialPhysical

end

end OAI
