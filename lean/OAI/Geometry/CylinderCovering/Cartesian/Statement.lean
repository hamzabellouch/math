import OAI.Geometry.CylinderCovering.Cartesian.StatementDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.Domain

namespace OAI

namespace CylinderCovering.CartesianCaps

theorem cartesianAperture_proved : CylinderCovering.CartesianApertureStatement := by
  intro τ η hτ hη
  have hcap := cap_properties τ η hτ hη
  refine ⟨hcap.1, hcap.2, ?_⟩
  intro b hb
  have harea := domain_area_bounds τ η b hτ hη hb
  exact ⟨domain_isCompact τ η b hb.2, domain_radial τ η b hτ hη hb, harea⟩

end CylinderCovering.CartesianCaps

end OAI
