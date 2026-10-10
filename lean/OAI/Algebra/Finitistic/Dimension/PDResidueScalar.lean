import OAI.Algebra.Finitistic.Dimension.PDResidueRing

namespace OAI
noncomputable section
namespace LittleFinitistic.PDResidueScalar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Name the generic residue scalar structure so concrete square-zero algebras
need not unfold their entire construction during typeclass search. -/
@[instance_reducible] def moduleK : Module k (PDTensor.Residue (A := A)) := inferInstance

attribute [local instance] moduleK

theorem towerK : IsScalarTower k Aᵐᵒᵖ (PDTensor.Residue (A := A)) := inferInstance
end LittleFinitistic.PDResidueScalar

end

end OAI
