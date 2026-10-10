import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.InitialAlphabet

namespace OAI

section Inline_PCPInitialSize
namespace MetricKMedian.PCP.InitialAlphabet
open scoped Classical

variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
lemma box_edges (C : BinaryCSP V E A) : (box A C).edges=Nat.card E*(4*Nat.card (AlphabetReduction.EdgeSample A)) := by
  change Fintype.card (AlphabetReduction.Test (E := E) (K := A) × Fin 4)=_
  simp only [AlphabetReduction.Test,Fintype.card_prod,Fintype.card_fin,Nat.card_eq_fintype_card]
  ring
end MetricKMedian.PCP.InitialAlphabet

end Inline_PCPInitialSize

end OAI
