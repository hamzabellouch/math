import OAI.Combinatorics.Crossing.OrderedCrossingPorts

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem crossingChord_parameter_interior (C : DrawingPassages D.toFiniteIntersectionDrawing) (p : C.InnerIndex)
    (t : unitInterval) (ht : C.crossingChord p t ∈ C.crossingDisk p) :
    t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 0-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.source,C.incomingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 1-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.target,C.outgoingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_crossing_disk_parameter_between (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : E.assembledEdge v p.1 t ∈ C.crossingDisk p) : u < t ∧ t < w := by
  obtain ⟨f,hf,he⟩ := E.assembledEdge_contains_chord v p
  have h0 : f 0=u := E.assembledEdge_injective v hv p.1
    (((he 0).trans (C.crossingChord p).source).trans hu.symm)
  have h1 : f 1=w := E.assembledEdge_injective v hv p.1
    (((he 1).trans (C.crossingChord p).target).trans hw.symm)
  have hmem : E.assembledEdge v p.1 t ∈ Set.range (C.crossingChord p) :=
    (E.assembled_range_in_crossingDisk v hv p _ ht).mp ⟨t,rfl⟩
  obtain ⟨s,hs⟩ := hmem
  have hsint := C.crossingChord_parameter_interior p s (hs.symm ▸ ht)
  have hst : f s=t := E.assembledEdge_injective v hv p.1 ((he s).trans hs)
  exact ⟨by simpa only [h0,hst] using hf hsint.1,by simpa only [h1,hst] using hf hsint.2⟩

theorem assembled_crossing_port_clearance (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : t ≤ u ∨ w ≤ t) : E.assembledEdge v p.1 t ∉ C.crossingDisk p := by
  intro hmem
  have hbetween := E.assembled_crossing_disk_parameter_between v hv p u w hu hw t hmem
  rcases ht with ht | ht
  · exact hbetween.1.not_ge ht
  · exact hbetween.2.not_ge ht

end PolygonalExterior
end Zarankiewicz

end

end OAI
