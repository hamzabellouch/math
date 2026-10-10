import OAI.Geometry.CylinderCovering.Beams.NeighborhoodDefinitions
import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Beams.sDefinitions
import OAI.Geometry.CylinderCovering.Beams.CostDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.BeamNeighborhoodRealization
open Set MeasureTheory RadialSweep

def physicalMap (D : Data) (z : BeamNeighborhood.Plane) : Space :=
  D.p₀ + (z 0 + z 1) • D.a + z 0 • D.b

def rawBase (D : Data) (a l r δ : ℝ) : Set Space :=
  physicalMap D '' BeamNeighborhood.paddedSector a l r δ

def base (D : Data) (a l r δ : ℝ) : Set Space :=
  TriangularCovering.projection (direction D ((l+r)/2)) '' rawBase D a l r δ

def cellBase (D : Data) (a : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  base D a (RadialRiemann.point 0 1 N i) (RadialRiemann.point 0 1 N (i+1))
    (RadialRiemann.step 0 1 N)

def cost (D : Data) (a : ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin N, TriangularCovering.area (cellBase D a N i)

def cellMidpoint (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point 0 1 N i+RadialRiemann.point 0 1 N (i+1))/2

def beamBaseMinus (a : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (ShortenedBeam.axisMinus a (cellMidpoint N i)) ''
    ((fun z : BeamNeighborhood.Plane => ShortenedBeam.point (-1+z 0) (-1+z 1) 0) ''
      BeamNeighborhood.paddedSector a (RadialRiemann.point 0 1 N i)
        (RadialRiemann.point 0 1 N (i+1)) (RadialRiemann.step 0 1 N))

def beamBasePlus (a : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (ShortenedBeam.axisPlus a (cellMidpoint N i)) ''
    ((fun z : BeamNeighborhood.Plane => ShortenedBeam.point (1-z 0) (1-z 1) 0) ''
      BeamNeighborhood.paddedSector a (RadialRiemann.point 0 1 N i)
        (RadialRiemann.point 0 1 N (i+1)) (RadialRiemann.step 0 1 N))

def alternativeCost (a : ℝ) (N : ℕ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area (beamBaseMinus a N i))+
    ∑ i : Fin N, TriangularCovering.area (beamBasePlus a N i)

def AlternativeStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    (∀ i : Fin N,
      ‖ShortenedBeam.axisMinus a (cellMidpoint N i)‖ = 1 ∧
      ‖ShortenedBeam.axisPlus a (cellMidpoint N i)‖ = 1 ∧
      IsCompact (beamBaseMinus a N i) ∧ IsCompact (beamBasePlus a N i) ∧
      MeasurableSet (beamBaseMinus a N i) ∧ MeasurableSet (beamBasePlus a N i) ∧
      Measure.euclideanHausdorffMeasure 2 (beamBaseMinus a N i) ≠ ⊤ ∧
      Measure.euclideanHausdorffMeasure 2 (beamBasePlus a N i) ≠ ⊤ ∧
      (∀ z ∈ beamBaseMinus a N i, inner ℝ (ShortenedBeam.axisMinus a (cellMidpoint N i)) z=0) ∧
      (∀ z ∈ beamBasePlus a N i, inner ℝ (ShortenedBeam.axisPlus a (cellMidpoint N i)) z=0)) ∧
    (∀ z ∈ ShortenedBeam.beamMinus a, ∃ i : Fin N,
      z ∈ cylinder (ShortenedBeam.axisMinus a (cellMidpoint N i)) (beamBaseMinus a N i)) ∧
    (∀ z ∈ ShortenedBeam.beamPlus a, ∃ i : Fin N,
      z ∈ cylinder (ShortenedBeam.axisPlus a (cellMidpoint N i)) (beamBasePlus a N i)) ∧
    alternativeCost a N ≤ (Real.sqrt 2/4)*BeamCost.beamCost a+C/(N:ℝ)

end CylinderCovering.BeamNeighborhoodRealization

end

end OAI
