import OAI.Combinatorics.Crossing.RetainedArcDisjointness

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

abbrev Port (C : DrawingPassages D) := C.ArcIndex × Bool

def portPoint (C : DrawingPassages D) (p : C.Port) : Plane :=
  if p.2 then C.arcEnd p.1 else C.arcStart p.1

def portMark (C : DrawingPassages D) (p : C.Port) : DrawingMark D :=
  if p.2 then C.arcEndMark p.1 else C.arcStartMark p.1

theorem portPoint_mem_arc (C : DrawingPassages D) (p : C.Port) :
    C.portPoint p ∈ Set.range (C.arc p.1) := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact ⟨0,(C.arc i).source⟩
  · exact ⟨1,(C.arc i).target⟩

theorem portPoint_injective (C : DrawingPassages D) : Function.Injective C.portPoint := by
  rintro ⟨i,s⟩ ⟨j,t⟩ he
  have hij : i=j := by
    by_contra h
    exact Set.disjoint_left.mp (C.arcs_pairwise_disjoint i j h)
      (C.portPoint_mem_arc (i,s)) (he.symm ▸ C.portPoint_mem_arc (j,t))
  subst j
  have hst : s=t := by
    cases s <;> cases t
    · rfl
    · exact False.elim (C.arc_endpoints_ne i he)
    · exact False.elim (C.arc_endpoints_ne i he.symm)
    · rfl
  subst t
  rfl

theorem portPoint_on_circle (C : DrawingPassages D) (p : C.Port) :
    squaredLength (C.portPoint p-(C.portMark p).val)=C.radius^2 := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact C.arc_start_on_circle i
  · exact C.arc_end_on_circle i

abbrev PortsAt (C : DrawingPassages D) (x : DrawingMark D) := {p : C.Port // C.portMark p=x}

theorem portsAt_on_circle (C : DrawingPassages D) (x : DrawingMark D) (p : C.PortsAt x) :
    squaredLength (C.portPoint p.val-x.val)=C.radius^2 := by
  simpa only [p.property] using C.portPoint_on_circle p.val

end Zarankiewicz.DrawingPassages

end

end OAI
