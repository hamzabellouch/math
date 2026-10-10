import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.AngularGeneral

def planarSector (D : Data) (j : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∃ q ∈ interval D j, ∃ s ∈ Set.Icc (0 : ℝ) (D.radius j q),
    p = WithLp.toLp 2 ![q * s, s]}

end CylinderCovering.AngularGeneral

end

end OAI
