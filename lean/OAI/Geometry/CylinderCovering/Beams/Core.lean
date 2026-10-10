import OAI.Geometry.CylinderCovering.Beams.FullDefinitions
import OAI.Geometry.CylinderCovering.Beams.Main
import OAI.Geometry.CylinderCovering.Beams.ShapeCompact
import OAI.Geometry.CylinderCovering.Beams.Geometry

namespace OAI

noncomputable section
namespace ShortenedBeam

theorem finiteMixedFullStatement : FiniteMixedStatement := by
  intro a ha ha' ε hε
  obtain ⟨n,C,hC,hcover,hcost⟩ := finiteMixedStatement a ε ha ha' hε
  exact ⟨n,C,fun i => ⟨hC i,(hC i).isCompact⟩,hcover,hcost⟩

theorem primaryConstruction :
    CoverageStatement ∧ FiniteBeamsStatement ∧ FiniteStripStatement ∧
    CylinderCovering.BeamCost.CostStatement ∧ FiniteMixedStatement ∧
    CanonicalCounterexampleStatement ∧ RegularCounterexampleStatement :=
  ⟨coverageStatement, finiteBeamsStatement, finiteStripStatement,
    CylinderCovering.BeamCost.fullCost, finiteMixedFullStatement,
    canonicalCounterexample, regularMixedCounterexample⟩

theorem full_of_geometry_and_neighborhood
    (hgeometry : GeometryStatement) (hneighborhood : NeighborhoodAlternativeStatement) :
    FullStatement :=
  ⟨hgeometry, coverageStatement, finiteBeamsStatement, finiteStripStatement,
    CylinderCovering.BeamCost.fullCost, finiteMixedFullStatement,
    canonicalCounterexample, regularMixedCounterexample, hneighborhood⟩

theorem primaryConstructionWithGeometry :
    GeometryStatement ∧ CoverageStatement ∧ FiniteBeamsStatement ∧ FiniteStripStatement ∧
    CylinderCovering.BeamCost.CostStatement ∧ FiniteMixedStatement ∧
    CanonicalCounterexampleStatement ∧ RegularCounterexampleStatement :=
  ⟨geometryStatement, primaryConstruction⟩

theorem full_of_neighborhood (h : NeighborhoodAlternativeStatement) : FullStatement :=
  full_of_geometry_and_neighborhood geometryStatement h

end ShortenedBeam

end

end OAI
