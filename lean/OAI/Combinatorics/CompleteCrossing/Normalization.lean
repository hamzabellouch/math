import OAI.Combinatorics.CompleteCrossing.CirclePlacement
import OAI.Combinatorics.CompleteCrossing.Subdivision
import OAI.Combinatorics.CompleteCrossing.SurgeryIntersections
import OAI.Combinatorics.CompleteCrossing.Truncation
import OAI.Combinatorics.Crossing.ReconnectedVertexAvoidance
import OAI.Combinatorics.Crossing.ReducedPolygonalPresentation

namespace OAI

/-! Reorientation invariance and normalization without adjacent crossings or crossing knots. -/

section

/-! Reversing chosen oriented representatives changes no spatial drawing or crossing count. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170
variable {V E : Type}

def Graph.reorient (G : Graph V E) (reverse : E → Bool) : Graph V E where
  src e := if reverse e = true then G.dst e else G.src e
  dst e := if reverse e = true then G.src e else G.dst e
  loopless e := by
    by_cases h : reverse e = true
    · simpa only [ite_eq_left h] using (G.loopless e).symm
    · simpa only [ite_eq_right h] using G.loopless e
  simple e f h := by
    apply G.simple e f
    by_cases he : reverse e = true <;> by_cases hf : reverse f = true <;>
      simp [he,hf] at h <;> tauto

theorem unitInterval_symm_mem_Ioo (t : unitInterval) :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 ↔ t ∈ Ioo (0 : unitInterval) 1 := by
  change (0 < 1-(t : ℝ) ∧ 1-(t : ℝ) < 1) ↔ (0 < (t : ℝ) ∧ (t : ℝ) < 1)
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

namespace ContinuousDrawing
variable {G : Graph V E}

def reorientedPath (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    Path (D.vertex ((G.reorient reverse).src e)) (D.vertex ((G.reorient reverse).dst e)) :=
  if h : reverse e = true then (D.edge e).symm.cast
    (by simp only [Graph.reorient,ite_eq_left h]) (by simp only [Graph.reorient,ite_eq_left h])
  else (D.edge e).cast
    (by simp only [Graph.reorient,ite_eq_right h]) (by simp only [Graph.reorient,ite_eq_right h])

theorem reorientedPath_apply (D : ContinuousDrawing G) (reverse : E → Bool) (e : E)
    (t : unitInterval) : D.reorientedPath reverse e t =
      if reverse e = true then D.edge e (unitInterval.symm t) else D.edge e t := by
  unfold reorientedPath
  split <;> rfl

def reorient (D : ContinuousDrawing G) (reverse : E → Bool) :
    ContinuousDrawing (G.reorient reverse) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.reorientedPath reverse
  edge_injective e := by
    intro s t hst
    rw [reorientedPath_apply,reorientedPath_apply] at hst
    by_cases h : reverse e = true
    · rw [ite_eq_left h,ite_eq_left h] at hst
      exact unitInterval.symm_bijective.1 (D.edge_injective e hst)
    · rw [ite_eq_right h,ite_eq_right h] at hst
      exact D.edge_injective e hst
  interior_avoids_vertices e t ht v := by
    rw [reorientedPath_apply]
    by_cases h : reverse e = true
    · rw [ite_eq_left h]
      exact D.interior_avoids_vertices e _ ((unitInterval_symm_mem_Ioo t).mpr ht) v
    · rw [ite_eq_right h]
      exact D.interior_avoids_vertices e t ht v

theorem reorient_edgeInterior (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    edgeInterior (D.reorient reverse) e = edgeInterior D e := by
  ext x
  by_cases h : reverse e = true
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,ite_eq_left h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e (unitInterval.symm t) = x
      simpa only [reorientedPath_apply,ite_eq_left h,unitInterval.symm_symm] using hx
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,ite_eq_right h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x
      simpa only [reorientedPath_apply,ite_eq_right h] using hx

theorem reorient_crossingPoints (D : ContinuousDrawing G) (reverse : E → Bool) :
    crossingPoints (D.reorient reverse) = crossingPoints D := by
  ext x
  simp only [crossingPoints, mem_ofPred_eq, reorient_edgeInterior]

end ContinuousDrawing

namespace AdmissibleDrawing
variable {G : Graph V E}

def reorient (D : AdmissibleDrawing G) (reverse : E → Bool) :
    AdmissibleDrawing (G.reorient reverse) where
  toContinuousDrawing := D.toContinuousDrawing.reorient reverse
  crossings_finite := by
    rw [ContinuousDrawing.reorient_crossingPoints]
    exact D.crossings_finite
  crossings_proper e f hef x he hf := by
    rw [ContinuousDrawing.reorient_edgeInterior] at he hf
    rw [ContinuousDrawing.reorient_edgeInterior,ContinuousDrawing.reorient_edgeInterior]
    exact D.crossings_proper e f hef x he hf
  no_triples e f g hef heg hfg := by
    simp only [ContinuousDrawing.reorient_edgeInterior]
    exact D.no_triples e f g hef heg hfg

theorem reorient_crossingCount (D : AdmissibleDrawing G) (reverse : E → Bool) :
    crossingCount (D.reorient reverse) = crossingCount D := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, reorient, ContinuousDrawing.reorient_crossingPoints]

end AdmissibleDrawing
end Paper170

end
end

section

/-! Reorientation preserves the minimum property among ordinary drawings. -/
noncomputable section
namespace Paper170
variable {V E : Type}

theorem Graph.eq_of_endpoints {G H : Graph V E} (hs : G.src = H.src)
    (ht : G.dst = H.dst) : G = H := by
  cases G
  cases H
  cases hs
  cases ht
  rfl

theorem Graph.reorient_reorient (G : Graph V E) (reverse : E → Bool) :
    (G.reorient reverse).reorient reverse = G := by
  apply Graph.eq_of_endpoints
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]

namespace AdmissibleDrawing
variable {G H : Graph V E}

def castGraph (h : G = H) (D : AdmissibleDrawing G) : AdmissibleDrawing H := h ▸ D

theorem castGraph_crossingCount (h : G = H) (D : AdmissibleDrawing G) :
    crossingCount (D.castGraph h) = crossingCount D := by
  cases h
  rfl

theorem reorient_minimal (D : AdmissibleDrawing G) (reverse : E → Bool)
    (hmin : ∀ A : AdmissibleDrawing G, crossingCount D ≤ crossingCount A) :
    ∀ A : AdmissibleDrawing (G.reorient reverse),
      crossingCount (D.reorient reverse) ≤ crossingCount A := by
  intro A
  have h := hmin ((A.reorient reverse).castGraph (G.reorient_reorient reverse))
  simpa only [castGraph_crossingCount,reorient_crossingCount] using h

end AdmissibleDrawing
end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {G : Graph V E}

def reparametrizedContinuous (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path) : ContinuousDrawing G where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge e := (P e).path
  edge_injective := hP
  interior_avoids_vertices e t ht v :=
    Zarankiewicz.path_interior_avoids_vertices_of_range D.vertex (G.src e) (G.dst e)
      (P e).path (hP e) (by
        intro w hw
        obtain ⟨s, hs⟩ := (P e).path_range_subset hw
        rcases Paper170Geometry.drawing_edge_vertex_parameter D e s w hs with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2) t ht v

lemma reparametrized_interior (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) (e : E) :
    edgeInterior (reparametrizedContinuous D P hP) e = edgeInterior D e := by
  ext x
  constructor
  · intro hx
    apply Paper170Geometry.edgeInterior_of_range_not_vertices D e x
    · rw [← htrace e]
      exact Paper170Geometry.edgeInterior_subset_range _ e hx
    · exact Paper170Geometry.edgeInterior_not_vertex (reparametrizedContinuous D P hP) e x hx
  · intro hx
    apply Paper170Geometry.edgeInterior_of_range_not_vertices (reparametrizedContinuous D P hP) e x
    · change x ∈ range (P e).path
      rw [htrace e]
      exact Paper170Geometry.edgeInterior_subset_range D e hx
    · exact Paper170Geometry.edgeInterior_not_vertex D e x hx

lemma reparametrized_crossings (D : ContinuousDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) :
    crossingPoints (reparametrizedContinuous D P hP) = crossingPoints D := by
  ext x
  simp only [crossingPoints, reparametrized_interior D P hP htrace]

def reparametrizedDrawing (D : AdmissibleDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) : AdmissibleDrawing G where
  toContinuousDrawing := reparametrizedContinuous D.toContinuousDrawing P hP
  crossings_finite := by
    rw [reparametrized_crossings D.toContinuousDrawing P hP htrace]
    exact D.crossings_finite
  crossings_proper := by
    intro e f hef x he hf
    simp only [reparametrized_interior D.toContinuousDrawing P hP htrace] at he hf ⊢
    exact D.crossings_proper e f hef x he hf
  no_triples := by
    intro e f g hef heg hfg
    simp only [reparametrized_interior D.toContinuousDrawing P hP htrace]
    exact D.no_triples e f g hef heg hfg

lemma reparametrized_count (D : AdmissibleDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) :
    crossingCount (reparametrizedDrawing D P hP htrace) = crossingCount D := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset]
  change x ∈ crossingPoints (reparametrizedContinuous D.toContinuousDrawing P hP) ↔ _
  rw [reparametrized_crossings D.toContinuousDrawing P hP htrace]

lemma normalized_of_locally_straight [Fintype V] (D : AdmissibleDrawing G)
    (hpoly : ∀ e, Zarankiewicz.HasFiniteAffineCover (D.edge e))
    (hnoadj : Paper170Geometry.NoAdjacentCrossings D)
    (hstraight : Paper170Geometry.LocallyStraightCrossings D) :
    ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing = crossingCount D := by
  have hp (e : E) : ∃ P : Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)),
      range P.path = range (D.edge e) ∧ Function.Injective P.path ∧ 0 < P.pieces ∧
      ∀ Q : Zarankiewicz.PolygonalChain (range (D.edge e))
        (D.vertex (G.src e)) (D.vertex (G.dst e)), P.pieces ≤ Q.pieces := by
    obtain ⟨P, ht, hi, hn, _, _, hm⟩ :=
      Zarankiewicz.exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
    exact ⟨P, ht, hi, hn, hm⟩
  choose P htrace hinj hpos hmin using hp
  have hq (e : E) : ∃ Q : PolygonalParametrization (P e).path,
      ∀ i, (P e).path (Q.knot i) ∉ crossingPoints D.toContinuousDrawing :=
    chain_subdivision_avoiding (P e) (hpos e) {x | x ∉ crossingPoints D.toContinuousDrawing}
      (Paper170Geometry.minimum_vertices_not_crossing D hstraight e (P e) (hmin e))
  choose Q hQ using hq
  let N : NormalizedDrawing G := {
    toAdmissibleDrawing := reparametrizedDrawing D P hinj htrace
    polygonal := Q
    no_adjacent := by
      intro e f hef hinc
      change Disjoint (edgeInterior (reparametrizedContinuous D.toContinuousDrawing P hinj) e)
        (edgeInterior (reparametrizedContinuous D.toContinuousDrawing P hinj) f)
      simp only [reparametrized_interior D.toContinuousDrawing P hinj htrace]
      exact Set.disjoint_iff_inter_eq_empty.mpr (hnoadj.eq_empty e f hef hinc)
    crossings_not_knots := by
      intro e i
      change (P e).path ((Q e).knot i) ∉
        crossingPoints (reparametrizedContinuous D.toContinuousDrawing P hinj)
      rw [reparametrized_crossings D.toContinuousDrawing P hinj htrace]
      exact hQ e i }
  exact ⟨N, reparametrized_count D P hinj htrace⟩

end Paper170

end
end

section

/-! The assembled ordinary drawing is genuinely straight near every crossing. -/
noncomputable section
namespace Paper170Geometry
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace PolygonalExterior
variable {D : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_locallyStraightCrossings (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyStraightCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  constructor
  intro e f hef x hx hy
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hpx := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hqx := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  have hlocal (r : C.InnerIndex) (hr : x ∈ C.crossingDisk r)
      (hxr : x ∈ Set.range (C.crossingChord r)) :
      LocallyStraightAt (E.assembledDrawing v hvinj hv) r.1 x := by
    constructor
    refine ⟨C.portPoint (C.incomingPort r),C.portPoint (C.outgoingPort r),
      C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort r r),
      (C.crossingChord_openTrace_iff r x hr).mp hxr,C.crossingDisk r,C.crossingDisk_isOpen r,hr,?_⟩
    exact E.assembled_trace_in_crossingDisk v hvinj hv r
  change LocallyStraightAt (E.assembledDrawing v hvinj hv) e x ∧
    LocallyStraightAt (E.assembledDrawing v hvinj hv) f x
  exact ⟨by simpa only [hp] using hlocal p hpx hxp,by simpa only [hq] using hlocal q hqx hxq⟩

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Minimum ordinary drawings have no crossing between any pair sharing a vertex. -/
noncomputable section
namespace Paper170Geometry
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Paper170.Graph Vertex Edge}

theorem minimum_no_common_source_or_target (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A)
    (e f : Edge) (hef : e ≠ f)
    (hadj : graph.src e = graph.src f ∨ graph.dst e = graph.dst f) :
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxe,hxf⟩
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D :=
    le_antisymm (E.assembled_crossingCount_le v hvinj hv hdet) (hmin _)
  obtain ⟨y,hye,hyf⟩ := E.assembled_pair_retained_of_count_eq v hvinj hv hdet hcount e f hef x hxe hxf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (edgeInterior_not_vertex (E.assembledDrawing v hvinj hv) e y hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) e hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) f hyf)
  have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
  have hadj' : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1 := by
    simpa only [hp,hq] using hadj
  obtain ⟨R,hRpoly,hRcount⟩ := E.exists_admissible_adjacent_surgery
    v hvinj hv hdet p q hpq hadj' y hyp hyq
  rw [hcount] at hRcount
  exact (not_lt_of_ge (hmin R)) hRcount

theorem minimum_no_adjacent (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A) : NoAdjacentCrossings D := by
  constructor
  intro e f hef hadj
  obtain ⟨i,he,hf⟩ : ∃ i, (graph.src e = i ∨ graph.dst e = i) ∧
      (graph.src f = i ∨ graph.dst f = i) := by
    rcases hadj with h | h | h | h
    · exact ⟨graph.src e,Or.inl rfl,Or.inl h.symm⟩
    · exact ⟨graph.src e,Or.inl rfl,Or.inr h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inl h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inr h.symm⟩
  let reverse : Edge → Bool := fun a => decide (graph.dst a = i)
  have hsource (a : Edge) (ha : graph.src a = i ∨ graph.dst a = i) :
      (graph.reorient reverse).src a = i := by
    simp only [Paper170.Graph.reorient,reverse,decide_eq_true_eq]
    split
    · assumption
    · exact ha.resolve_right (by assumption)
  have h := minimum_no_common_source_or_target (D.reorient reverse)
    (D.reorient_minimal reverse hmin) e f hef
    (Or.inl ((hsource e he).trans (hsource f hf).symm))
  simpa only [Paper170.AdmissibleDrawing.reorient,
    Paper170.ContinuousDrawing.reorient_edgeInterior] using h

theorem exists_minimum_assembled (D : Paper170.AdmissibleDrawing graph) :
    ∃ (B : Paper170.AdmissibleDrawing graph) (C : DrawingPassages B.toFiniteIntersectionDrawing)
      (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-B.vertex j) < C.radius^2)
      (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
        det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0),
      NoAdjacentCrossings (E.assembledAdmissible v hvinj hv hdet) ∧
        Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
          Paper170.ordinaryCrossingNumber graph := by
  obtain ⟨B,hB⟩ := crossingCount_attainment D
  obtain ⟨C⟩ := nonempty_drawingPassages B.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  let A := E.assembledAdmissible v hvinj hv hdet
  have hcount : Paper170.crossingCount A = Paper170.ordinaryCrossingNumber graph := by
    apply le_antisymm
    · exact (E.assembled_crossingCount_le v hvinj hv hdet).trans_eq hB
    · exact ordinaryCrossingNumber_le_count A
  refine ⟨B,C,E,v,hvinj,hv,hdet,minimum_no_adjacent A ?_,hcount⟩
  intro R
  rw [hcount]
  exact ordinaryCrossingNumber_le_count R

theorem polygonal_no_adjacent_locally_straight (D : Paper170.AdmissibleDrawing graph) :
    ∃ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount A = Paper170.ordinaryCrossingNumber graph ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧ LocallyStraightCrossings A := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_minimum_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,hcount,E.assembledEdge_hasFiniteAffineCover v,
    hnorm,E.assembled_locallyStraightCrossings v hvinj hv hdet⟩

end Paper170Geometry

end
end

section

noncomputable section
namespace Paper170
variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

theorem polygonal_no_adjacent_normalization (D : AdmissibleDrawing G) :
    ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing ≤ crossingCount D := by
  obtain ⟨A, hcount, hpoly, hnoadj, hstraight⟩ :=
    Paper170Geometry.polygonal_no_adjacent_locally_straight D
  obtain ⟨N, hN⟩ := normalized_of_locally_straight A hpoly hnoadj hstraight
  exact ⟨N, (hN.trans hcount).le.trans (Paper170Geometry.ordinaryCrossingNumber_le_count D)⟩

theorem normalized_minimum_exists :
    ∃ N : NormalizedDrawing G,
      crossingCount N.toAdmissibleDrawing = ordinaryCrossingNumber G := by
  obtain ⟨D, hD, _⟩ := minimum_drawing_exists G
  obtain ⟨N, hN⟩ := polygonal_no_adjacent_normalization G D
  exact ⟨N, le_antisymm (hN.trans_eq hD)
    (Paper170Geometry.ordinaryCrossingNumber_le_count N.toAdmissibleDrawing)⟩

end Paper170

end
end

end OAI
