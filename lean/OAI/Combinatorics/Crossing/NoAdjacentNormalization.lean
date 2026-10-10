import OAI.Combinatorics.Crossing.AdmissibleAdjacentSurgery
import OAI.Combinatorics.Crossing.RowCrossingCount

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_no_adjacent_assembled {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ (B : AdmissibleDrawing m n) (C : DrawingPassages B.toFiniteIntersectionDrawing)
      (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-B.vertex j) < C.radius^2)
      (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
        det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0),
      NoAdjacentCrossings (E.assembledAdmissible v hvinj hv hdet) ∧
        crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ crossingCount D := by
  classical
  induction hc : crossingCount D using Nat.strong_induction_on generalizing D with
  | h k ih =>
    obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
    obtain ⟨E⟩ := nonempty_polygonalExterior C
    obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
    let A := E.assembledAdmissible v hvinj hv hdet
    have hcount : crossingCount A ≤ crossingCount D := E.assembled_crossingCount_le v hvinj hv hdet
    by_cases hnorm : NoAdjacentCrossings A
    · exact ⟨D,C,E,v,hvinj,hv,hdet,hnorm,hcount.trans_eq hc⟩
    have hex : ∃ e f : BipartiteEdge m n, e ≠ f ∧ (e.1=f.1 ∨ e.2=f.2) ∧
        (edgeInterior A.toContinuousDrawing e ∩ edgeInterior A.toContinuousDrawing f).Nonempty := by
      by_contra hh
      apply hnorm
      intro e f hef hadj
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hh ⟨e,f,hef,hadj,x,hx⟩
    obtain ⟨e,f,hef,hadj,x,hxe,hxf⟩ := hex
    obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
      (edgeInterior_not_vertex A.toContinuousDrawing e x hxe)
      (edgeInterior_subset_range A.toContinuousDrawing e hxe)
      (edgeInterior_subset_range A.toContinuousDrawing f hxf)
    have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
    have hadj' : p.1.1=q.1.1 ∨ p.1.2=q.1.2 := by simpa only [hp,hq] using hadj
    obtain ⟨R,hRpoly,hRcount⟩ := E.exists_admissible_adjacent_surgery v hvinj hv hdet p q hpq hadj' x hxp hxq
    have hRk : crossingCount R < k := (hRcount.trans_le hcount).trans_eq hc
    obtain ⟨B,C',E',v',hvinj',hv',hdet',hnorm',hcount'⟩ := ih (crossingCount R) hRk R rfl
    exact ⟨B,C',E',v',hvinj',hv',hdet',hnorm',(hcount'.trans (hRcount.le.trans hcount)).trans_eq hc⟩

theorem polygonal_normalization_no_adjacent {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      NoAdjacentCrossings A ∧ crossingCount A ≤ crossingCount D := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_no_adjacent_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,hnorm,hcount⟩

end Zarankiewicz

end

end OAI
