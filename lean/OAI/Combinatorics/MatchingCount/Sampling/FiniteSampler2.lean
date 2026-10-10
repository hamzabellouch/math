import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Cycle

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace LongComponent

variable {p : PM inc × PM inc} (S : LongComponent p)

noncomputable instance : Fintype (LongComponent p) := Fintype.ofFinite _

end LongComponent

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance finiteSampler2BagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler2DemandBagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

noncomputable instance : Fintype (Demand hbags hG) := Fintype.ofFinite _

noncomputable instance : Fintype (ErrorDemand hbags hG) := Fintype.ofFinite _

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace PatternCode

variable (x : PatternCode inc)

variable [Fintype E]

noncomputable instance finiteSampler2PatternCodeFintype : Fintype (PatternCode inc) := Fintype.ofFinite _

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler2AcyclicBagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler2CellBagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler2ErrorBagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

end MatchingFPRAS.Transport.CellDemands

end OAI
