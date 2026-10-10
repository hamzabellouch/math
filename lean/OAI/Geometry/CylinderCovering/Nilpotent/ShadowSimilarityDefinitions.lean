import OAI.Geometry.CylinderCovering.Nilpotent.SimilarityDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Nilpotent
open RuledApproximation

def centerDirection (u : Space) : Space := vec3 (u 0) (u 1) (-u 2)

def ShadowSimilarityStatement : Prop :=
  (∀ u : Space, ‖centerDirection u‖ = ‖u‖) ∧
  (∀ (S : Set Space) (u : Space),
    shadowArea (centerMap '' S) (centerDirection u) = shadowArea S u / 4)

end CylinderCovering.Nilpotent

end

end OAI
