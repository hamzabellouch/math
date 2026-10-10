import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section
namespace CylinderCovering.RadialPairedSweep

def upperLocalSweep (h ε : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  {z | ∃ q ∈ RadialRiemann.cell (-1) 1 N i,
    ∃ ρ ∈ Icc (0 : ℝ) (R q), ∃ x : ℝ, |x| ≤ 2 ∧
      z = point x (ρ*q-ε*x*RadialCaps.G q) (h*(1-ρ+ε*x*q))}

def lowerLocalSweep (h ε : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  {z | ∃ q ∈ RadialRiemann.cell (-1) 1 N i,
    ∃ ρ ∈ Icc (0 : ℝ) (R q), ∃ y : ℝ, |y| ≤ 2 ∧
      z = point (ρ*q+ε*y*RadialCaps.G q) y (h*(-1+ρ+ε*y*q))}

def upperActualBase (h ε : ℝ) (R : ℝ → ℝ) (N : ℕ)
    (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (upperAxis h ε (tag i)) '' upperLocalSweep h ε R N i

def lowerActualBase (h ε : ℝ) (R : ℝ → ℝ) (N : ℕ)
    (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (lowerAxis h ε (tag i)) '' lowerLocalSweep h ε R N i

def pairedActualCost (h ε : ℝ) (R : ℝ → ℝ) (N : ℕ)
    (tagU tagL : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area (upperActualBase h ε R N tagU i)) +
  (∑ i : Fin N, TriangularCovering.area (lowerActualBase h ε R N tagL i))

def ActualBaseProperties (u : Space) (B : Set Space) : Prop :=
  ‖u‖ = 1 ∧ IsCompact B ∧ MeasurableSet B ∧
    Measure.euclideanHausdorffMeasure 2 B ≠ ⊤ ∧
    (∀ z ∈ B, inner ℝ u z = 0)

def ActualPairedStatement : Prop :=
  ∀ h ε : ℝ, 0 < h → ∀ R : ℝ → ℝ,
    ContinuousOn R (Icc (-1 : ℝ) 1) → (∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q) →
    ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
    (∀ N, 0 < N →
      (∀ i : Fin N,
        ActualBaseProperties (upperAxis h ε (tagU N i))
          (upperActualBase h ε R N (tagU N) i) ∧
        ActualBaseProperties (lowerAxis h ε (tagL N i))
          (lowerActualBase h ε R N (tagL N) i)) ∧
      (∀ z ∈ upperSweep h ε R, ∃ i : Fin N,
        z ∈ RadialSweep.cylinder (upperAxis h ε (tagU N i))
          (upperActualBase h ε R N (tagU N) i)) ∧
      (∀ z ∈ lowerSweep h ε R, ∃ i : Fin N,
        z ∈ RadialSweep.cylinder (lowerAxis h ε (tagL N i))
          (lowerActualBase h ε R N (tagL N) i))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      pairedActualCost h ε R N (tagU N) (tagL N) ≤ 2*h*physicalCost h ε R + δ) ∧
    Filter.limsup (fun N => pairedActualCost h ε R N (tagU N) (tagL N)) atTop ≤
      2*h*physicalCost h ε R

end CylinderCovering.RadialPairedSweep

end

end OAI
