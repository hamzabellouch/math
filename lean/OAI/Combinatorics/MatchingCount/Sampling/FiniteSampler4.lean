import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.PM
import OAI.Combinatorics.MatchingCount.Graphs.Density

namespace OAI


namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler4BagEdgeFintype : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)



open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler4BagEdgeFintype2 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG



open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance finiteSampler4BagEdgeFintype3 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype4 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype5 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype6 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance finiteSampler4PMDecidableEq : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype7 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance finiteSampler4WeightedPMDecidableEq : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype8 : Fintype (BagEdge bags) := Fintype.ofFinite _



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype9 : Fintype (BagEdge bags) := Fintype.ofFinite _



open Finset MatchingFPRAS.Replica

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance finiteSampler4BagEdgeFintype10 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport

end OAI
