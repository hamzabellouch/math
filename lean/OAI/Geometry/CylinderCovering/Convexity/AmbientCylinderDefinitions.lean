import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set

namespace RuledApproximation

def Cylinder.fromAmbientBase (u : Space) (hu : ‖u‖ = 1) (B : Set Space) : Cylinder :=
  ⟨u, hu, (Subtype.val : ((Submodule.span ℝ ({u} : Set Space))ᗮ) → Space) ⁻¹' B⟩

end RuledApproximation

end

end OAI
