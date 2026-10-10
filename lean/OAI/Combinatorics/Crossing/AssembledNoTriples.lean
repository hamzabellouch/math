import OAI.Combinatorics.Crossing.AssembledCrossings

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_no_triples (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f g : BipartiteEdge m n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (E.assembledDrawing v hvinj hv) e ∩
      edgeInterior (E.assembledDrawing v hvinj hv) f ∩
      edgeInterior (E.assembledDrawing v hvinj hv) g=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨⟨s,hs,he⟩,⟨t,ht,hf⟩⟩,⟨u,hu,hg⟩⟩
  have ha : ∀ j, x ≠ v j := fun j heq =>
    E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x ha ⟨s,he⟩ ⟨t,hf⟩
  obtain ⟨r,z,hr,hz,hxr,hxz⟩ := E.assembled_meeting_chords v hv hdet e g heg x ha ⟨s,he⟩ ⟨u,hg⟩
  apply C.innerMark_no_triples p q z
  · intro heq
    exact hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  · intro heq
    exact heg (hp.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · intro heq
    exact hfg (hq.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · exact C.chord_meeting_marks_eq p q hxp hxq
  · exact C.chord_meeting_marks_eq p z hxp hxz

end Zarankiewicz.PolygonalExterior

end

end OAI
