import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

namespace OAI

namespace Balanced
namespace TailGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

def slotVertices (slot : V → I) (i : I) : Finset V :=
  Finset.univ.filter (fun v => slot v = i)

def slotSize (slot : V → I) (i : I) : ℕ :=
  (slotVertices slot i).card

def edgeSlots (slot : V → I) (e : Sym2 V) : Finset I :=
  e.toFinset.image slot

noncomputable def edgeWeight (slot : V → I) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    2 / ((slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ)),
    fun u v => by simp only [mul_comm]⟩

def slotEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I) (i : I) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => i ∈ edgeSlots slot e)

def touchingEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (J : Finset I) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ i ∈ J, i ∈ edgeSlots slot e)

def dependencyEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (e : Sym2 V) : Finset (Sym2 V) :=
  (touchingEdges G slot (edgeSlots slot e)).erase e

def NoWithinSlotEdges (G : SimpleGraph V) (slot : V → I) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → slot u ≠ slot v

end TailGraph
end Balanced

end OAI
