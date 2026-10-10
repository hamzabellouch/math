import OAI.Geometry.CylinderCovering.Beams.MainDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ShortenedBeam

def vertices : Fin 4 → Space :=
  ![point 2 0 (-1), point (-2) 0 (-1), point 0 2 1, point 0 (-2) 1]

def GeometryStatement : Prop :=
  tetrahedron = convexHull ℝ (range vertices) ∧ AffineIndependent ℝ vertices ∧
  (∀ i j : Fin 4, i ≠ j → dist (vertices i) (vertices j) = 2*Real.sqrt 2) ∧
  volume.real tetrahedron = 8/3 ∧
  CylinderCovering.minimumShadowArea tetrahedron = 2*Real.sqrt 2

abbrev MixedShape := HasMixedBase

def FiniteMixedStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 → ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, MixedShape (C i) ∧ IsCompact (C i).base) ∧
      tetrahedron ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C ≤
        (Real.sqrt 2/4)*(CylinderCovering.BeamCost.beamCost a+
          CylinderCovering.BeamCost.stripCost a)+ε

abbrev RegularCounterexampleStatement := RegularMixedCounterexampleStatement

abbrev ParameterPlane := EuclideanSpace ℝ (Fin 2)

def doubleSector (a : ℝ) (N : ℕ) (i : Fin N) : Set ParameterPlane :=
  {z | ∃ p ∈ CylinderCovering.RadialRiemann.cell 0 1 N i,
    ∃ r ∈ Icc (-(1/(N:ℝ))) ((2-a)+1/(N:ℝ)),
      z = !₂[r*p,r*(1-p)]}

def midpointTag (N : ℕ) (i : Fin N) : ℝ :=
  (CylinderCovering.RadialRiemann.point 0 1 N i+
    CylinderCovering.RadialRiemann.point 0 1 N (i+1))/2

def neighborhoodSector (a : ℝ) (N : ℕ) (i : Fin N) : Set ParameterPlane :=
  Metric.cthickening ((1/(N:ℝ))^2) (doubleSector a N i)

def neighborhoodBaseMinus (a : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (axisMinus a (midpointTag N i)) ''
    ((fun z : ParameterPlane => point (-1+z 0) (-1+z 1) 0) '' neighborhoodSector a N i)

def neighborhoodBasePlus (a : ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (axisPlus a (midpointTag N i)) ''
    ((fun z : ParameterPlane => point (1-z 0) (1-z 1) 0) '' neighborhoodSector a N i)

def NeighborhoodAlternativeStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 →
    ∃ errorConstant : ℝ, 0 ≤ errorConstant ∧
    ∃ Cminus Cplus : (N : ℕ) → Fin N → RuledApproximation.Cylinder,
      ∀ N : ℕ, 0 < N →
        (∀ i : Fin N,
          (Cminus N i).axis = axisMinus a (midpointTag N i) ∧
          (Cplus N i).axis = axisPlus a (midpointTag N i) ∧
          Subtype.val '' (Cminus N i).base = neighborhoodBaseMinus a N i ∧
          Subtype.val '' (Cplus N i).base = neighborhoodBasePlus a N i ∧
          IsCompact (Cminus N i).base ∧ IsCompact (Cplus N i).base) ∧
        beamMinus a ⊆ RuledApproximation.familySet (Cminus N) ∧
        beamPlus a ⊆ RuledApproximation.familySet (Cplus N) ∧
        (RuledApproximation.familyArea (Cminus N)+RuledApproximation.familyArea (Cplus N)) /
            (Real.sqrt 2/4) ≤
          CylinderCovering.BeamCost.beamCost a+errorConstant/(N:ℝ)

def FullStatement : Prop :=
  GeometryStatement ∧ CoverageStatement ∧ FiniteBeamsStatement ∧ FiniteStripStatement ∧
  CylinderCovering.BeamCost.CostStatement ∧ FiniteMixedStatement ∧
  CanonicalCounterexampleStatement ∧ RegularCounterexampleStatement ∧
  NeighborhoodAlternativeStatement

end ShortenedBeam

end

end OAI
