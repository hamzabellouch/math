import OAI.Combinatorics.Crossing.DrawingVertexPlacement

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def firstArc (C : DrawingPassages D) (e : BipartiteEdge m n) : C.ArcIndex :=
  ⟨e,⟨0,C.count_pos e⟩⟩

def lastArc (C : DrawingPassages D) (e : BipartiteEdge m n) : C.ArcIndex :=
  ⟨e,⟨C.count e-1,by have h := C.count_pos e; omega⟩⟩

theorem lastArc_node (C : DrawingPassages D) (e : BipartiteEdge m n) :
    (C.lastArc e).2.succ=Fin.last (C.count e) := by
  apply Fin.ext
  have h := C.count_pos e
  change C.count e-1+1=C.count e
  omega

theorem firstArc_mark (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.arcStartMark (C.firstArc e)=C.vertexMark (.inl e.1) := by
  apply Subtype.ext
  change D.edge e (C.node e 0)=D.vertex (.inl e.1)
  rw [C.first,Path.source]

theorem lastArc_mark (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.arcEndMark (C.lastArc e)=C.vertexMark (.inr e.2) := by
  apply Subtype.ext
  change D.edge e (C.node e (C.lastArc e).2.succ)=D.vertex (.inr e.2)
  rw [C.lastArc_node,C.last,Path.target]

def startPortAt (C : DrawingPassages D) (e : BipartiteEdge m n) : C.PortsAt (C.vertexMark (.inl e.1)) :=
  ⟨(C.firstArc e,false),C.firstArc_mark e⟩

def endPortAt (C : DrawingPassages D) (e : BipartiteEdge m n) : C.PortsAt (C.vertexMark (.inr e.2)) :=
  ⟨(C.lastArc e,true),C.lastArc_mark e⟩

end Zarankiewicz.DrawingPassages

end

end OAI
