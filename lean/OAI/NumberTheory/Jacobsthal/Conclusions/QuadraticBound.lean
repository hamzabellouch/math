import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalFromRootLower
import OAI.NumberTheory.Jacobsthal.Conclusions.SourceRootCompletion

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final


theorem erdos_970_quadratic : NumberTheoryLean.Targets.JacobsthalQuadratic := by
  obtain ⟨c,hc,hLower⟩ := source_root_survivor_lower
  exact NumberTheoryLean.JacobsthalFromRootLower.jacobsthal_of_source_root_lower c hc
    (ErdosCorrectionLimit.sourceRootNode (1/100)) hLower

end Erdos970Final


end Erdos970

end OAI
