import OAI.Combinatorics.Crossing.DrawingPorts
import OAI.Combinatorics.Crossing.RoundCircleChords

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

abbrev InnerIndex (C : DrawingPassages D) :=
  (e : BipartiteEdge m n) × {i : Fin (C.count e+1) // 0 < i.val ∧ i.val < C.count e}

def innerMark (C : DrawingPassages D) (p : C.InnerIndex) : DrawingMark D :=
  ⟨D.edge p.1 (C.node p.1 p.2.val),C.node_mark p.1 p.2.val⟩

def incomingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val-1,by have h := p.2.property; omega⟩⟩

def outgoingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val,p.2.property.2⟩⟩

def incomingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.incomingArc p,true)
def outgoingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.outgoingArc p,false)

theorem incoming_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.incomingArc p).2.succ=p.2.val := by
  apply Fin.ext
  change p.2.val.val-1+1=p.2.val.val
  have h := p.2.property.1
  omega

theorem outgoing_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.outgoingArc p).2.castSucc=p.2.val := rfl

theorem incomingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.incomingPort p)=C.innerMark p := by
  apply Subtype.ext
  change D.edge p.1 (C.node p.1 (C.incomingArc p).2.succ)=D.edge p.1 (C.node p.1 p.2.val)
  rw [C.incoming_node]

theorem outgoingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.outgoingPort p)=C.innerMark p := rfl

theorem incomingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.incomingPort p)=D.edge p.1 (C.passage p.1 p.2.val).enter := by
  change D.edge p.1 (C.passage p.1 (C.incomingArc p).2.succ).enter=_
  rw [C.incoming_node]

theorem outgoingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.outgoingPort p)=D.edge p.1 (C.passage p.1 p.2.val).leave := rfl

theorem inner_parameter_interior (C : DrawingPassages D) (p : C.InnerIndex) :
    C.node p.1 p.2.val ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · rw [← C.first p.1]
    exact C.increasing p.1 (show (0 : Fin (C.count p.1+1)) < p.2.val from p.2.property.1)
  · rw [← C.last p.1]
    exact C.increasing p.1 (show p.2.val < Fin.last (C.count p.1) from p.2.property.2)

theorem innerMark_is_crossing (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.innerMark p).val ∈ crossingPoints D.toContinuousDrawing := by
  have hm := (C.innerMark p).property
  rcases hm with ⟨v,hv⟩ | hcross
  · exact False.elim (D.interior_avoids_vertices p.1 (C.node p.1 p.2.val)
      (C.inner_parameter_interior p) v hv.symm)
  · exact hcross

def crossingChord (C : DrawingPassages D) (p : C.InnerIndex) :
    Path (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) :=
  Path.segment _ _

theorem crossingChord_injective (C : DrawingPassages D) (p : C.InnerIndex) :
    Function.Injective (C.crossingChord p) := by
  apply Path.segment_injective_of_ne
  intro he
  rw [C.incomingPort_point,C.outgoingPort_point] at he
  exact (C.passage p.1 p.2.val).enter_lt_leave.ne (D.edge_injective p.1 he)

end Zarankiewicz.DrawingPassages

end

end OAI
