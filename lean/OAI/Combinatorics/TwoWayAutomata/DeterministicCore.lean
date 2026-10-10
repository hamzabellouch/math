import OAI.Combinatorics.TwoWayAutomata.Model

namespace OAI

namespace TwoWayComplementation

/-- At most one next-state/move pair at every state and scanned symbol. -/
def TwoNFA.Deterministic {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Prop :=
  ∀ q symbol, (A.transition q symbol).Subsingleton

end TwoWayComplementation

end OAI
