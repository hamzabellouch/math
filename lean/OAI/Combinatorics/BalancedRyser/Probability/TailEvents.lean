import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability
import OAI.Combinatorics.BalancedRyser.Probability.TailGraph

namespace OAI

namespace Balanced.TailGraph

variable {I : Type*} (Q : I → Type*)

def edgeEvent (e : Sym2 (Sigma Q)) : Set (Slots.Assignment Q) :=
  {ω | ∀ v ∈ e, ω v.1 = v.2}

end Balanced.TailGraph

end OAI
