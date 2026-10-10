import OAI.Geometry.CylinderCovering.Beams.Midsection
import OAI.Geometry.CylinderCovering.Beams.ExplicitTriangles
import OAI.Geometry.CylinderCovering.Beams.SectorGeometry
import OAI.Geometry.CylinderCovering.Beams.Core
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodIntrinsic

namespace OAI

noncomputable section
namespace ShortenedBeam

theorem fullConstruction : FullStatement :=
  full_of_neighborhood neighborhoodAlternativeStatement

end ShortenedBeam

end

end OAI
