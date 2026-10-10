import OAI.Geometry.CylinderCovering.Nilpotent.RateCertificatesDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.RatePhysical
import OAI.Geometry.CylinderCovering.Nilpotent.RateUniform

namespace OAI

noncomputable section
namespace CylinderCovering.NilpotentRate

theorem completeSmoothRate : CompleteSmoothRateStatement where
  smooth := smoothRate
  uniform := smoothRate_uniform
  physical := fun _δ _R _h hδ hh _D _G _tag _Q hfin a =>
    construction_physical_realization hδ hh hfin a

end CylinderCovering.NilpotentRate

end

end OAI
