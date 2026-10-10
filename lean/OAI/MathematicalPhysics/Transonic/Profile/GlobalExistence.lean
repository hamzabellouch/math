import OAI.MathematicalPhysics.Transonic.Profile.GlobalRadialProfile
import OAI.MathematicalPhysics.Transonic.Exterior.CoverAll
import OAI.MathematicalPhysics.Transonic.Shooting.MatchedExistence

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting

/-- Existence of a global smooth relativistic transonic profile at `ell = 5/3`. -/
theorem exists_global_source_profile : RelativisticProfileExists := by
  obtain ⟨M⟩ := exists_matched_pair
  obtain ⟨B⟩ := M.exists_exteriorBranch
    (ExteriorCertificates.actual_germ_window M.sonic.germ M.parameter)
  obtain ⟨T⟩ := B.exists_tail
  exact T.relativistic_profile

end SepticProfile.SonicShooting

end
end

end OAI
