import OAI.Geometry.CylinderCovering.Angular.ExtensionsDefinitions
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCover
import OAI.Geometry.CylinderCovering.Convexity.SquaredCapCover
import OAI.Geometry.CylinderCovering.Cartesian.Cover

namespace OAI

namespace CylinderCovering.AngularExtensions

theorem core : CoreStatement :=
  ⟨AngularGeneral.general_cap, AngularOrdinaryCaps.ordinary_covers,
    AngularCaps.squared_cap_cover, CartesianCaps.cartesian_cover⟩

end CylinderCovering.AngularExtensions

end OAI
