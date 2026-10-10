import OAI.Geometry.CylinderCovering.Barycentric.SectorDefinitions
import OAI.Geometry.CylinderCovering.Radial.TriangleDefinitions

namespace OAI

noncomputable section
open Set

namespace RadialCoordinates.BarycentricSector

def neighborhood (l r k M : ℝ) : Set Plane :=
  Metric.cthickening (Real.sqrt 2*k*(r-l)^2)
    (signedSector l r (2*k*(r-l)) (M+2*k*(r-l)))

def triangleChart (p : ℝ × ℝ) : Plane := !₂[p.2, p.1-p.2]

def neighborhoodTriangle (l r k M : ℝ) : Set Plane :=
  triangleChart '' CylinderCovering.RadialTriangle.region
    (-(12*k*(r-l))) (M+6*k*(r-l)) ((l+r)/2) (r-l)

end RadialCoordinates.BarycentricSector

end

end OAI
