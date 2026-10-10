import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Uniformization.FiniteJordanImageUniformization

namespace OAI

/-! Finite circle models from an invariant Beltrami solution and boundary
reflection, without a finite uniformization hypothesis. -/
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem finiteJordanModelUniformization : FiniteJordanModelUniformization := by
  intro n H hd e
  exact exists_finite_jordan_image_uniformization ⟨H,hd⟩ e

end CircleDomainRigidity

end

end OAI
