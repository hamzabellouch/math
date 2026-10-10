import OAI.Combinatorics.Crossing.DrawingPassages
import OAI.Combinatorics.Crossing.IntervalSegmentStrict
import OAI.Combinatorics.Crossing.FiniteDiskCollar

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

abbrev ArcIndex (C : DrawingPassages D) := (e : BipartiteEdge m n) × Fin (C.count e)

theorem node_mark (C : DrawingPassages D) (e : BipartiteEdge m n) (i : Fin (C.count e+1)) :
    D.edge e (C.node e i) ∈ drawingMarks D := by
  change C.node e i ∈ (D.edge e) ⁻¹' drawingMarks D
  rw [← C.node_range e]
  exact ⟨i,rfl⟩

def arcStartMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.castSucc),C.node_mark i.1 i.2.castSucc⟩

def arcEndMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.succ),C.node_mark i.1 i.2.succ⟩

def arcStart (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.castSucc).leave

def arcEnd (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.succ).enter

def arc (C : DrawingPassages D) (i : C.ArcIndex) : Path (C.arcStart i) (C.arcEnd i) :=
  retainedSubarc (D.edge i.1) (C.node i.1) C.radius (C.passage i.1) i.2

theorem arc_gap (C : DrawingPassages D) (i : C.ArcIndex) :
    (C.passage i.1 i.2.castSucc).leave < (C.passage i.1 i.2.succ).enter :=
  C.separated i.1 i.2.castSucc i.2.succ (by change i.2.val < i.2.val+1; omega)

theorem arc_injective (C : DrawingPassages D) (i : C.ArcIndex) : Function.Injective (C.arc i) :=
  pathSubarc_injective (D.edge i.1) (D.edge_injective i.1) _ _ (C.arc_gap i)

theorem arc_endpoints_ne (C : DrawingPassages D) (i : C.ArcIndex) : C.arcStart i ≠ C.arcEnd i := by
  intro he
  exact (C.arc_gap i).ne (D.edge_injective i.1 he)

theorem arc_range (C : DrawingPassages D) (i : C.ArcIndex) :
    Set.range (C.arc i)=D.edge i.1 '' Set.Icc (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter :=
  pathSubarc_range (D.edge i.1) _ _ (C.arc_gap i)

theorem arc_avoids_marks (C : DrawingPassages D) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (C.arc i)) : x ∉ drawingMarks D := by
  rw [C.arc_range] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  intro hh
  have hp : t ∈ Set.range (C.node i.1) := by rw [C.node_range]; exact hh
  exact retained_interval_no_mark (D.edge i.1) (C.node i.1) (C.increasing i.1)
    (C.first i.1) (C.last i.1) C.radius (C.passage i.1) i.2 t ht hp

theorem retained_parameter_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter) :
    D.edge i.1 t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  intro x
  apply lt_of_not_ge
  intro hh
  obtain ⟨u,hu⟩ := C.visited_mark_on_edge i.1 x t hh
  have hmu : u ∈ Set.range (C.node i.1) := by
    rw [C.node_range]
    change D.edge i.1 u ∈ drawingMarks D
    rw [hu]
    exact x.property
  obtain ⟨j,hj⟩ := hmu
  have hc : D.edge i.1 (C.node i.1 j)=x.val := (congrArg (D.edge i.1) hj).trans hu
  have hv := (C.passage i.1 j).all_visits t (by rw [hc]; exact hh)
  by_cases hji : j ≤ i.2.castSucc
  · have hm := (ordered_passage_leave_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hji
    exact ht.1.not_ge (hv.2.trans hm)
  · have hij : i.2.succ ≤ j := by
      change i.2.val+1 ≤ j.val
      have hn : ¬ j.val ≤ i.2.val := hji
      omega
    have hm := (ordered_passage_enter_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hij
    exact ht.2.not_ge (hm.trans hv.1)

theorem arc_interior_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    C.arc i t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  exact C.retained_parameter_outside i _ (intervalSegment_strict_between _ _ t (C.arc_gap i) ht)

theorem arc_start_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcStart i-(C.arcStartMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.castSucc).leave_boundary
    ((C.arc_gap i).trans_le (show (C.passage i.1 i.2.succ).enter ≤ 1 from (C.passage i.1 i.2.succ).enter.property.2))

theorem arc_end_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcEnd i-(C.arcEndMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.succ).enter_boundary
    ((show 0 ≤ (C.passage i.1 i.2.castSucc).leave from (C.passage i.1 i.2.castSucc).leave.property.1).trans_lt (C.arc_gap i))

end Zarankiewicz.DrawingPassages

end

end OAI
