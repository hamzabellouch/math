import OAI.Combinatorics.CompleteCrossing.DrawingMarks
import OAI.Combinatorics.Crossing.CurveDiskIsolation
import OAI.Combinatorics.Crossing.FiniteDiskCollar
import OAI.Combinatorics.Crossing.IntervalSegmentStrict
import OAI.Combinatorics.Crossing.OrderedPassages

namespace OAI

/-! Isolated drawing disks, retained arcs, and boundary ports. -/

section

/-! The actual finite vertex/crossing marks supply the normalization disk family. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
abbrev DrawingMark (D : FiniteIntersectionDrawing graph) := ↥(drawingMarks D)

theorem drawing_disk_isolation [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ δ : Edge → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ x y : DrawingMark D, x ≠ y →
        Disjoint (closedRoundDisk x.val r) (closedRoundDisk y.val r)) ∧
      (∀ e (x : DrawingMark D) t, D.edge e t ∈ closedRoundDisk x.val r →
        ∃ u : unitInterval, D.edge e u=x.val ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, D.edge e u ∈ drawingMarks D → D.edge e v ∈ drawingMarks D → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  let : DecidableEq (DrawingMark D) := Classical.decEq _
  obtain ⟨δ,r,hδ,hr,hd,hv,hs⟩ := finite_injective_curve_disk_isolation
    (fun e => D.edge e) (fun e => (D.edge e).continuous) D.edge_injective
    (fun x : DrawingMark D => x.val) Subtype.val_injective
  refine ⟨δ,r,hδ,hr,hd,hv,?_⟩
  intro e u v hu hv huv
  exact hs e u v ⟨⟨D.edge e u,hu⟩,rfl⟩ ⟨⟨D.edge e v,hv⟩,rfl⟩ huv

end Paper170Geometry

end
end

section

/-! Constructed finite marked-passage decomposition of the given actual drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
/-- Geometric cut data for the original drawing. Existence is proved below;
this record asserts no crossing bound or drawing-normalization conclusion. -/
structure DrawingPassages (D : FiniteIntersectionDrawing graph) where
  radius : ℝ
  radius_pos : 0 < radius
  disks_disjoint : ∀ x y : DrawingMark D, x ≠ y →
    Disjoint (closedRoundDisk x.val radius) (closedRoundDisk y.val radius)
  count : Edge → ℕ
  count_pos : ∀ e, 0 < count e
  node : ∀ e, Fin (count e+1) → unitInterval
  increasing : ∀ e, StrictMono (node e)
  first : ∀ e, node e 0=0
  last : ∀ e, node e (Fin.last (count e))=1
  node_range : ∀ e, Set.range (node e)=(D.edge e) ⁻¹' drawingMarks D
  passage : ∀ e i, DiskPassage (D.edge e) (D.edge e (node e i)) radius (node e i)
  separated : ∀ e i j, i < j → (passage e i).leave < (passage e j).enter
  visited_mark_on_edge : ∀ e (x : DrawingMark D) t,
    D.edge e t ∈ closedRoundDisk x.val radius → ∃ u, D.edge e u=x.val

theorem nonempty_drawingPassages [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) : Nonempty (DrawingPassages D) := by
  classical
  obtain ⟨δ,r,hδ,hr,hdisks,hvisits,hparam⟩ := drawing_disk_isolation D
  choose k hk τ hτ h0 h1 hR using (fun e => exists_sorted_drawing_parameters D e)
  have hnode (e : Edge) (i : Fin (k e+1)) : D.edge e (τ e i) ∈ drawingMarks D := by
    change τ e i ∈ (D.edge e) ⁻¹' drawingMarks D
    rw [← hR e]
    exact ⟨i,rfl⟩
  have hex (e : Edge) (i : Fin (k e+1)) :
      Nonempty (DiskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)) :=
    nonempty_diskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)
      (by simpa [squaredLength] using sq_pos_of_pos hr)
  let P (e : Edge) (i : Fin (k e+1)) := Classical.choice (hex e i)
  have hlocal (e : Edge) (i : Fin (k e+1)) (t : unitInterval)
      (ht : D.edge e t ∈ closedRoundDisk (D.edge e (τ e i)) r) :
      t ∈ parameterNeighborhood (τ e i) (δ e) := by
    obtain ⟨u,hu,hh⟩ := hvisits e ⟨D.edge e (τ e i),hnode e i⟩ t ht
    have he : u=τ e i := D.edge_injective e hu
    simpa [he] using hh
  have hsep (e : Edge) (i j : Fin (k e+1)) (hij : i < j) :
      (P e i).leave < (P e j).enter := by
    apply diskPassage_separated (P e i) (P e j) (hτ e hij) (hδ e)
    · exact hparam e (τ e i) (τ e j) (hnode e i) (hnode e j) ((hτ e).injective.ne (ne_of_lt hij))
    · exact hlocal e i _ (P e i).leave_mem
    · exact hlocal e j _ (P e j).enter_mem
  exact ⟨{
    radius := r
    radius_pos := hr
    disks_disjoint := hdisks
    count := k
    count_pos := hk
    node := τ
    increasing := hτ
    first := h0
    last := h1
    node_range := hR
    passage := P
    separated := hsep
    visited_mark_on_edge := fun e x t ht => by
      obtain ⟨u,hu,_⟩ := hvisits e x t ht
      exact ⟨u,hu⟩ }⟩

end Paper170Geometry

end
end

section

/-! Actual retained middle arcs: endpoint circles and avoidance of every disk and mark. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

abbrev ArcIndex (C : DrawingPassages D) := (e : Edge) × Fin (C.count e)

theorem node_mark (C : DrawingPassages D) (e : Edge) (i : Fin (C.count e+1)) :
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

end Paper170Geometry.DrawingPassages

end
end

section

/-! The retained actual compact arcs are pairwise disjoint, including on the same edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem arcs_pairwise_disjoint (C : DrawingPassages D) (p q : C.ArcIndex) (hpq : p ≠ q) :
    Disjoint (Set.range (C.arc p)) (Set.range (C.arc q)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxm := C.arc_avoids_marks p x hx
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  rw [C.arc_range] at hx hy
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  have hef : e=f := unmarked_intersection_same_edge D e f s t (hsx.trans htx.symm)
    (hsx.symm ▸ hxm)
  subst f
  have hst : s=t := D.edge_injective e (hsx.trans htx.symm)
  rw [← hst] at ht
  have hij : i ≠ j := by
    intro he
    subst j
    exact hpq rfl
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) i j hij) hs ht
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) j i hji) ht hs

end Paper170Geometry.DrawingPassages

end
end

section

/-! The actual distinct disk-boundary endpoints of all retained arcs. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

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

end Paper170Geometry.DrawingPassages

end
end

end OAI
