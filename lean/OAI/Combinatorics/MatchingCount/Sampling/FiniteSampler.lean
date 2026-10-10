import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.PM

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance finiteSamplerBagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

include hheight hstep

end MatchingFPRAS.Transport.IndexedCycle

end OAI
