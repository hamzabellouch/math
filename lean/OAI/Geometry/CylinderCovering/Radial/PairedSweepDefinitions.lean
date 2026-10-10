import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions
import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section

namespace CylinderCovering.RadialPairedSweep

abbrev Space := TriangularCovering.Space

def point (x y z : ℝ) : Space := !₂[x, y, z]

def tetrahedron (h : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, |x| ≤ 1 + t ∧ |y| ≤ 1 - t ∧ z = point x y (h * t)}

def upperSweep (h ε : ℝ) (R : ℝ → ℝ) : Set Space :=
  {z | ∃ q ∈ Icc (-1 : ℝ) 1, ∃ ρ ∈ Icc (0 : ℝ) (R q),
    ∃ x : ℝ, |x| ≤ 2 ∧
      z = point x (ρ * q - ε * x * RadialCaps.G q) (h * (1 - ρ + ε * x * q))}

def lowerSweep (h ε : ℝ) (R : ℝ → ℝ) : Set Space :=
  {z | ∃ q ∈ Icc (-1 : ℝ) 1, ∃ ρ ∈ Icc (0 : ℝ) (R q),
    ∃ y : ℝ, |y| ≤ 2 ∧
      z = point (ρ * q + ε * y * RadialCaps.G q) y (h * (-1 + ρ + ε * y * q))}

def upperAxis (h ε q : ℝ) : Space :=
  let v := point 1 (-ε * RadialCaps.G q) (h * ε * q)
  ‖v‖⁻¹ • v

def lowerAxis (h ε q : ℝ) : Space :=
  let v := point (ε * RadialCaps.G q) 1 (h * ε * q)
  ‖v‖⁻¹ • v

def physicalCost (h ε : ℝ) (R : ℝ → ℝ) : ℝ :=
  ∫ q in (-1 : ℝ)..1,
    R q ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * (RadialCaps.G q ^ 2 + h ^ 2 * q ^ 2)))

def PairedStatement : Prop :=
  ∀ h ε : ℝ, 0 < h → ∀ R : ℝ → ℝ,
    ContinuousOn R (Icc (-1 : ℝ) 1) → (∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q) →
    ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
    ∃ U L : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i, (U N i).axis = upperAxis h ε (tagU N i) ∧
          (L N i).axis = lowerAxis h ε (tagL N i)) ∧
        (∀ z ∈ upperSweep h ε R, ∃ i : Fin N, z ∈ (U N i).carrier) ∧
        (∀ z ∈ lowerSweep h ε R, ∃ i : Fin N, z ∈ (L N i).carrier)) ∧
      Tendsto (fun N => TriangularCovering.totalArea (U N) +
        TriangularCovering.totalArea (L N)) atTop (𝓝 (2 * h * physicalCost h ε R))

end CylinderCovering.RadialPairedSweep

end

end OAI
