import OAI.Geometry.CylinderCovering.Radial.CoordinatesDefinitions

namespace OAI

noncomputable section
open Set

namespace RadialCoordinates.BarycentricSector

def positiveSector (l r A : ℝ) : Set Plane :=
  {z | ∃ t ∈ Icc l r, ∃ ρ ∈ Icc (0 : ℝ) A, z = ρ • ray t}

def signedSector (l r a b : ℝ) : Set Plane :=
  {z | ∃ t ∈ Icc l r, ∃ ρ ∈ Icc (-a) b, z = ρ • ray t}

def vertices (l r A : ℝ) : Fin 3 → Plane :=
  ![0, A • ray l, A • ray r]

def perimeter (l r A : ℝ) : ℝ :=
  dist (0 : Plane) (A • ray l) + dist (A • ray l) (A • ray r) +
    dist (A • ray r) 0

end RadialCoordinates.BarycentricSector

end

end OAI
