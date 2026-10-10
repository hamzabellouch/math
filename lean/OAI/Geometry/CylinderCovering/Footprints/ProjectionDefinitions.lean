import OAI.Geometry.CylinderCovering.Footprints.FootprintsDefinitions
import OAI.Geometry.TriangularCovering.Basic

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory
open scoped InnerProductSpace

def coordinateFootprint (p₀ a b : TriangularCovering.Space) (S : Set (ℝ × ℝ)) :
    Set TriangularCovering.Space :=
  (fun p : ℝ × ℝ => p₀ + p.1 • a + p.2 • b) '' S

def projectedCoordinateFootprint (e w p₀ a b : TriangularCovering.Space)
    (S : Set (ℝ × ℝ)) : Set TriangularCovering.Space :=
  TriangularCovering.projection (‖e + w‖⁻¹ • (e + w)) '' coordinateFootprint p₀ a b S

end RadialFootprints

end

end OAI
