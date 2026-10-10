import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects

namespace OAI

section Inline_PCPAdviceInstances
namespace MetricKMedian.PCP.Compiler
open scoped Classical

noncomputable instance adviceFintype {D A : Type} [Fintype D] [Fintype A] (cap:ℕ) : Fintype (Advice D A cap) := by
  unfold Advice
  infer_instance
end MetricKMedian.PCP.Compiler

end Inline_PCPAdviceInstances

end OAI
