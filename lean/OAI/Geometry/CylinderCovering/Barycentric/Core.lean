import OAI.Geometry.CylinderCovering.Barycentric.CoreDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.Coverage
import OAI.Geometry.CylinderCovering.Barycentric.SweepCompact
import OAI.Geometry.CylinderCovering.Barycentric.Cost

namespace OAI

namespace RadialCoordinates

theorem barycentricCore : CylinderCovering.BarycentricCoreStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨firstSweep_isCompact k, secondSweep_isCompact k⟩
  · intro k hk hkbound
    exact barycentric_simplex_covered hk hkbound
  · intro k hk
    exact J_expansion hk
  · intro k hk hkbound
    exact J_strict_half_target hk hkbound
  · intro a b z ha hb
    exact CylinderCovering.BarycentricRadial.existsUnique_parameter ha hb z
  · intro a b z ha hb
    exact CylinderCovering.BarycentricRadial.exists_nonnegative_radial_representation ha hb z

end RadialCoordinates

end OAI
