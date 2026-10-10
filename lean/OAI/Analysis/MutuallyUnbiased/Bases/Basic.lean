import Mathlib.Analysis.InnerProductSpace.PiL2
import OAI.Analysis.MutuallyUnbiased.Matrix.Definitions
import OAI.Analysis.MutuallyUnbiased.Model

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

/-- Maximum expressed as a supremum of attainable finite family sizes. -/
def N6 : ℕ := sSup {n : ℕ | Attainable n}

end MUB6

end

end OAI
