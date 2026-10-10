import Mathlib

namespace OAI

namespace MetricKMedianRecovery.IndexedCopies
@[instance_reducible]
def order (V : Type*) [LinearOrder V] : LinearOrder (V × Bool) :=
  LinearOrder.lift' (fun p : V × Bool => toLex p) (by intro a b h; exact h)
end MetricKMedianRecovery.IndexedCopies

end OAI
