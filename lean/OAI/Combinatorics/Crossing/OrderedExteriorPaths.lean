import OAI.Combinatorics.Crossing.AlternatingPaths
import OAI.Combinatorics.Crossing.ExteriorChordMeeting
import OAI.Combinatorics.Crossing.CrossingDiskIncidence
import OAI.Combinatorics.Crossing.VertexEndpointPorts

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def orderedArc (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ) : C.ArcIndex :=
  ⟨e,⟨min i (C.count e-1),by have h := C.count_pos e; omega⟩⟩

theorem orderedArc_val (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ)
    (hi : i < C.count e) : (C.orderedArc e i).2.val=i := by
  change min i (C.count e-1)=i
  omega

theorem orderedArc_inj (C : DrawingPassages D) (e : BipartiteEdge m n) (i j : ℕ)
    (hi : i < C.count e) (hj : j < C.count e)
    (h : C.orderedArc e i=C.orderedArc e j) : i=j := by
  have hh := congrArg (fun p : C.ArcIndex => p.2.val) h
  simpa only [C.orderedArc_val e i hi,C.orderedArc_val e j hj] using hh

theorem orderedArc_first (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.orderedArc e 0=C.firstArc e := by
  simp [orderedArc,firstArc]

theorem orderedArc_last (C : DrawingPassages D) (e : BipartiteEdge m n) :
    C.orderedArc e (C.count e-1)=C.lastArc e := by
  simp [orderedArc,lastArc]

def orderedInner (C : DrawingPassages D) (e : BipartiteEdge m n) (j : ℕ)
    (hj : j+1 < C.count e) : C.InnerIndex :=
  ⟨e,⟨⟨j+1,by omega⟩,⟨Nat.succ_pos j,hj⟩⟩⟩

theorem orderedInner_incoming (C : DrawingPassages D) (e : BipartiteEdge m n)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.incomingArc (C.orderedInner e j hj)=C.orderedArc e j := by
  unfold incomingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1-1=min j (C.count e-1)
  omega

theorem orderedInner_outgoing (C : DrawingPassages D) (e : BipartiteEdge m n)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.outgoingArc (C.orderedInner e j hj)=C.orderedArc e (j+1) := by
  unfold outgoingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1=min (j+1) (C.count e-1)
  omega

theorem orderedInner_inj (C : DrawingPassages D) (e : BipartiteEdge m n) (i j : ℕ)
    (hi : i+1 < C.count e) (hj : j+1 < C.count e)
    (h : C.orderedInner e i hi=C.orderedInner e j hj) : i=j := by
  have hh : i+1=j+1 := congrArg (fun p : C.InnerIndex => p.2.val.val) h
  omega

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

def orderedPath (E : PolygonalExterior C) (e : BipartiteEdge m n) (i : ℕ) :
    Path (C.arcStart (C.orderedArc e i)) (C.arcEnd (C.orderedArc e i)) :=
  (E.chain (C.orderedArc e i)).path

def orderedBridge (C : DrawingPassages D) (e : BipartiteEdge m n) (i : ℕ) :
    Path (C.arcEnd (C.orderedArc e i)) (C.arcStart (C.orderedArc e (i+1))) := Path.segment _ _

theorem orderedBridge_apply (e : BipartiteEdge m n) (j : ℕ) (hj : j+1 < C.count e)
    (t : unitInterval) :
    orderedBridge C e j t=C.crossingChord (C.orderedInner e j hj) t := by
  change (Path.segment _ _ : Path _ _) t=(Path.segment _ _ : Path _ _) t
  have ha : C.portPoint (C.incomingPort (C.orderedInner e j hj))=C.arcEnd (C.orderedArc e j) := by
    change C.arcEnd (C.incomingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_incoming]
  have hb : C.portPoint (C.outgoingPort (C.orderedInner e j hj))=C.arcStart (C.orderedArc e (j+1)) := by
    change C.arcStart (C.outgoingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_outgoing]
  simp only [Path.segment_apply,ha,hb]

theorem orderedBridge_range (e : BipartiteEdge m n) (j : ℕ) (hj : j+1 < C.count e) :
    Set.range (orderedBridge C e j)=Set.range (C.crossingChord (C.orderedInner e j hj)) := by
  congr 1
  funext t
  exact orderedBridge_apply e j hj t

def middlePath (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Path (C.arcStart (C.orderedArc e 0)) (C.arcEnd (C.orderedArc e (C.count e-1))) :=
  alternatingPath (fun i => C.arcStart (C.orderedArc e i))
    (fun i => C.arcEnd (C.orderedArc e i)) (E.orderedPath e) (orderedBridge C e) (C.count e-1)

end PolygonalExterior
end Zarankiewicz

end

end OAI
