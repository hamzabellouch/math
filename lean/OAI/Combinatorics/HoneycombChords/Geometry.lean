import OAI.Combinatorics.HoneycombChords.PathComponents
import Mathlib

namespace OAI

/-!
# Honeycomb centers, ports and simple chords

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb
open scoped ENNReal

abbrev Center := ℤ × ℤ × Bool

def up (i j : ℤ) : Center := (i, j, true)
def down (i j : ℤ) : Center := (i, j, false)

/-- Adjacency across a full triangular edge. -/
def Adj (v w : Center) : Prop :=
  if v.2.2 then
    w.2.2 = false ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 - 1) ∨
      (w.1 = v.1 - 1 ∧ w.2.1 = v.2.1))
  else
    w.2.2 = true ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 + 1) ∨
      (w.1 = v.1 + 1 ∧ w.2.1 = v.2.1))

noncomputable def rowSpacing : ℝ := Real.sqrt 3 / 2

/-- The fixed Euclidean embedding in the unit triangular tiling. -/
noncomputable def centerPosition (v : Center) : ℝ × ℝ :=
  if v.2.2 then
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1 / 2,
      rowSpacing * ((v.2.1 : ℝ) + 1 / 3))
  else
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1,
      rowSpacing * ((v.2.1 : ℝ) + 2 / 3))

/-- A midpoint port, oriented into the triangle domain. -/
structure Port (D : Set Center) where
  inside : Center
  outside : Center
  adjacent : Adj inside outside
  inside_mem : inside ∈ D
  outside_not_mem : outside ∉ D

noncomputable def Port.position {D : Set Center} (p : Port D) : ℝ × ℝ :=
  ((centerPosition p.inside).1 / 2 + (centerPosition p.outside).1 / 2,
    (centerPosition p.inside).2 / 2 + (centerPosition p.outside).2 / 2)

/-- A simple center trace, with no premature boundary exit. -/
def IsTrace (D : Set Center) (p : List Center) : Prop :=
  p.Nodup ∧ p.IsChain Adj ∧ ∀ v ∈ p, v ∈ D

def Chord (D : Set Center) (a b : Port D) :=
  {p : List Center // IsTrace D p ∧
    p.head? = some a.inside ∧ p.getLast? = some b.inside}

noncomputable def kappa : ℝ := (2 + Real.sqrt 2) ^ (-(1 : ℝ) / 2)

/-- Length counts centers; the port half-edges contribute no factors. -/
noncomputable def weight (p : List Center) : ℝ≥0∞ :=
  ENNReal.ofReal (kappa ^ p.length)

noncomputable def chordMass (D : Set Center) (a b : Port D) : ℝ≥0∞ :=
  ∑' p : Chord D a b, weight p.val


end CriticalHoneycomb

namespace CriticalHoneycomb.Transfer.FiniteConfigurations
open SimpleGraph

lemma adj_symmetric : ∀ ⦃v w : Center⦄, CriticalHoneycomb.Adj v w → CriticalHoneycomb.Adj w v := by
  rintro ⟨i,j,c⟩ ⟨k,l,d⟩ h
  cases c <;> cases d <;> simp_all [CriticalHoneycomb.Adj] <;> omega

lemma adj_irrefl (v : Center) : ¬ CriticalHoneycomb.Adj v v := by
  rcases v with ⟨i,j,c⟩
  cases c <;> simp [CriticalHoneycomb.Adj]

abbrev Interior (D : Finset Center) := {v // v ∈ D}
abbrev Vertices (D : Finset Center) := Interior D ⊕ Bool

def portInside {D : Finset Center} (a : Port (D : Set Center)) : Interior D :=
  ⟨a.inside,a.inside_mem⟩

def hardWallGraph (D : Finset Center) (a b : Port (D : Set Center)) :
    SimpleGraph (Vertices D) where
  Adj := portRel (fun x y : Interior D => CriticalHoneycomb.Adj x.val y.val)
    (portInside a) (portInside b)
  symm := ⟨by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact adj_symmetric h
      | inr q => cases q <;> exact h
    | inr q =>
      cases y with
      | inl y => cases q <;> exact h
      | inr r => cases q <;> cases r <;> exact h.elim⟩
  loopless := ⟨by
    intro v
    cases v with
    | inl v => exact adj_irrefl v.val
    | inr q => cases q <;> exact id⟩

/-- All hard-wall, unoriented 0/2-degree configurations with the two specified
ports occupied. This is finite graph data, not a probabilistic input. -/
structure Configuration (D : Finset Center) (a b : Port (D : Set Center)) where
  graph : SimpleGraph (Vertices D)
  allowed : graph ≤ hardWallGraph D a b
  port_degree : ∀ q : Bool, (graph.neighborSet (.inr q)).ncard = 1
  center_degree : ∀ v : Interior D,
    (graph.neighborSet (.inl v)).ncard = 0 ∨ (graph.neighborSet (.inl v)).ncard = 2

/-- The unique open component supplied by a local physical configuration is
an actual source center trace, with no other exit and with no repeated center.
Only the additionally detached cycle graph remains. -/
theorem configuration_contains_chord {D : Finset Center} {a b : Port (D : Set Center)}
    (C : Configuration D a b) :
    ∃ (γ : Chord (D : Set Center) a b) (xs : List (Interior D))
      (p : C.graph.Walk (.inr false) (.inr true)),
      xs.map Subtype.val = γ.val ∧ p.IsPath ∧
      p.support = Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true]) ∧
      (C.graph \ p.toSubgraph.spanningCoe).IsCycles := by
  classical
  have hp (q : Bool) : C.graph.degree (.inr q) = 1 := by
    rw [← PathComponents.ncard_neighbors]
    exact C.port_degree q
  have hc (v : Vertices D) (ha : v ≠ .inr false) (hb : v ≠ .inr true) :
      C.graph.degree v = 0 ∨ C.graph.degree v = 2 := by
    cases v with
    | inl v =>
      simpa only [PathComponents.ncard_neighbors] using C.center_degree v
    | inr q => cases q <;> contradiction
  obtain ⟨p,hp',hcycles,_⟩ := PathComponents.path_and_cycles C.graph
    (by simp : (Sum.inr false : Vertices D) ≠ .inr true) (hp false) (hp true) hc
  obtain ⟨xs,hxs,hn⟩ := support_decomposition p hp'
  have hch : p.support.IsChain (hardWallGraph D a b).Adj :=
    p.isChain_adj_support.imp (fun _ _ h => C.allowed h)
  rw [hxs] at hch
  have hch' := (chain_ports (fun x y : Interior D => CriticalHoneycomb.Adj x.val y.val)
    (portInside a) (portInside b) xs).mp hch
  let γ : Chord (D : Set Center) a b := ⟨xs.map Subtype.val, by
    refine ⟨⟨hn.map Subtype.val_injective,?_,?_⟩,?_,?_⟩
    · exact (List.isChain_map Subtype.val).mpr hch'.1
    · intro v hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
      exact x.property
    · rw [List.head?_map,hch'.2.1]
      rfl
    · rw [List.getLast?_map,hch'.2.2]
      rfl⟩
  exact ⟨γ,xs,p,rfl,hp',hxs,hcycles⟩

end CriticalHoneycomb.Transfer.FiniteConfigurations

namespace CriticalHoneycomb.Transfer.FiniteConfigurations
open SimpleGraph

/-- Conversely, every actual center chord determines a simple path in the
hard-wall graph with the exact two specified boundary markers. -/
theorem chord_has_hardWall_path {D : Finset Center} {a b : Port (D : Set Center)}
    (γ : Chord (D : Set Center) a b) :
    ∃ (xs : List (Interior D))
      (p : (hardWallGraph D a b).Walk (.inr false) (.inr true)),
      xs.map Subtype.val = γ.val ∧ p.IsPath ∧
      p.support = Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true]) := by
  let xs : List (Interior D) := γ.val.attach.map fun v =>
    ⟨v.val, γ.property.1.2.2 v.val v.property⟩
  have hmap : xs.map Subtype.val = γ.val := by
    simpa only [xs,List.map_map,Function.comp_def] using List.attach_map_subtype_val γ.val
  have hnd : xs.Nodup := List.Nodup.of_map _ (hmap.symm ▸ γ.property.1.1)
  have hchain : xs.IsChain (fun x y => CriticalHoneycomb.Adj x.val y.val) := by
    exact (List.isChain_map Subtype.val).mp (hmap.symm ▸ γ.property.1.2.1)
  have hhead : xs.head? = some (portInside a) := by
    apply Option.map_injective Subtype.val_injective
    change xs.head?.map Subtype.val = some a.inside
    rw [← List.head?_map,hmap]
    exact γ.property.2.1
  have hlast : xs.getLast? = some (portInside b) := by
    apply Option.map_injective Subtype.val_injective
    change xs.getLast?.map Subtype.val = some b.inside
    rw [← List.getLast?_map,hmap]
    exact γ.property.2.2
  let support : List (Vertices D) := Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true])
  have hne : support ≠ [] := List.cons_ne_nil _ _
  have hsc : support.IsChain (hardWallGraph D a b).Adj :=
    (chain_ports _ (portInside a) (portInside b) xs).mpr ⟨hchain,hhead,hlast⟩
  have hsh : support.head hne = .inr false := by rfl
  have hsl : support.getLast hne = .inr true := by simp [support]
  let p : (hardWallGraph D a b).Walk (.inr false) (.inr true) :=
    (Walk.ofSupport support hne hsc).copy hsh hsl
  have hps : p.support = support := by
    dsimp only [p]
    rw [Walk.support_copy,Walk.support_ofSupport]
  refine ⟨xs,p,hmap,?_,hps⟩
  rw [Walk.isPath_def,hps]
  simp [support,List.nodup_append,hnd.map Sum.inl_injective]
end CriticalHoneycomb.Transfer.FiniteConfigurations

namespace CriticalHoneycomb
/-- A full triangular edge indexed from its up-triangle side: middle,
south, west. All tensor wires are actual edges, not abstract crossings. -/
abbrev Wire := ℤ × ℤ × Fin 3

def neighbor (v : Center) (k : Fin 3) : Center :=
  if v.2.2 then down (v.1 - if k=2 then 1 else 0) (v.2.1 - if k=1 then 1 else 0)
  else up (v.1 + if k=2 then 1 else 0) (v.2.1 + if k=1 then 1 else 0)

def incidentWire (v : Center) (k : Fin 3) : Wire :=
  if v.2.2 then (v.1,v.2.1,k)
  else (v.1 + if k=2 then 1 else 0,v.2.1 + if k=1 then 1 else 0,k)

lemma neighbor_neighbor (v : Center) (k : Fin 3) : neighbor (neighbor v k) k = v := by
  rcases v with ⟨i,j,t⟩
  cases t <;> fin_cases k <;> simp [neighbor,up,down]

lemma neighbor_ne (v : Center) (k : Fin 3) : neighbor v k ≠ v := by
  rcases v with ⟨i,j,t⟩
  cases t <;> simp [neighbor,up,down]

lemma neighbor_injective (v : Center) : Function.Injective (neighbor v) := by
  rcases v with ⟨i,j,t⟩
  intro k l h
  cases t <;> fin_cases k <;> fin_cases l <;> simp_all [neighbor,up,down] <;> omega

lemma incidentWire_neighbor (v : Center) (k : Fin 3) :
    incidentWire (neighbor v k) k = incidentWire v k := by
  rcases v with ⟨i,j,t⟩
  cases t <;> fin_cases k <;> simp [neighbor,incidentWire,up,down]

lemma incidentWire_injective (v : Center) : Function.Injective (incidentWire v) := by
  intro k l h
  have hi := congrArg (fun w : Wire => w.2.2) h
  cases hv : v.2.2 <;> simpa [incidentWire,hv] using hi

lemma incidentWire_eq_iff (v w : Center) (k l : Fin 3) :
    incidentWire v k = incidentWire w l ↔ k=l ∧ (v=w ∨ neighbor v k=w) := by
  rcases v with ⟨i,j,t⟩
  rcases w with ⟨i',j',t'⟩
  cases t <;> cases t' <;> fin_cases k <;> fin_cases l <;>
    simp [incidentWire,neighbor,up,down,Prod.mk.injEq] <;> omega

lemma adj_iff_neighbor (v w : Center) : Adj v w ↔ ∃ k : Fin 3, neighbor v k=w := by
  rcases v with ⟨i,j,t⟩
  rcases w with ⟨i',j',t'⟩
  cases t <;> cases t' <;> simp [Adj,neighbor,up,down,Fin.exists_fin_succ] <;> omega

noncomputable def Port.side {D : Set Center} (p : Port D) : Fin 3 :=
  ((adj_iff_neighbor p.inside p.outside).mp p.adjacent).choose

lemma Port.neighbor_side {D : Set Center} (p : Port D) :
    neighbor p.inside p.side = p.outside :=
  ((adj_iff_neighbor p.inside p.outside).mp p.adjacent).choose_spec

noncomputable def Port.wire {D : Set Center} (p : Port D) : Wire :=
  incidentWire p.inside p.side

/-- A selected exterior midpoint may become a prescribed boundary vertex
only at its original inside center. -/
lemma Port.wire_eq_incident {D : Set Center} (p : Port D) {v : Center} (hv : v∈D)
    {k : Fin 3} (h : incidentWire v k=p.wire) : v=p.inside ∧ k=p.side := by
  have he := (incidentWire_eq_iff v p.inside k p.side).mp h
  have hk := he.1
  refine ⟨?_,hk⟩
  rcases he.2 with he | he
  · exact he
  · have ho : neighbor p.inside p.side = v := by rw [←he,←hk,neighbor_neighbor]
    exact False.elim (p.outside_not_mem (by rw [←p.neighbor_side,ho]; exact hv))

lemma Port.wire_ext {D : Set Center} (a b : Port D) (h : a.wire=b.wire) : a=b := by
  have he := b.wire_eq_incident a.inside_mem h
  have ho : a.outside=b.outside := by rw [←a.neighbor_side,←b.neighbor_side,he.1,he.2]
  cases a
  cases b
  simp_all

end CriticalHoneycomb

namespace CriticalHoneycomb.Transfer.FiniteConfigurations
open SimpleGraph

noncomputable def portAt {D : Finset Center} (a b : Port (D : Set Center))
    (q : Bool) : Port (D : Set Center) := if q then b else a

/-- Occupied actual midpoint edges, with only the two prescribed exits. -/
def BoundarySelection {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) : Prop :=
  s a.wire=true ∧ s b.wire=true ∧ ∀ v∈D, ∀ k : Fin 3,
    neighbor v k ∉ D → s (incidentWire v k)=true →
      incidentWire v k=a.wire ∨ incidentWire v k=b.wire

def selectedRel {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) : Vertices D → Vertices D → Prop
  | .inl v,.inl w => ∃ k : Fin 3, neighbor v.val k=w.val ∧ s (incidentWire v.val k)=true
  | .inl v,.inr q => v.val=(portAt a b q).inside ∧ s (portAt a b q).wire=true
  | .inr q,.inl v => v.val=(portAt a b q).inside ∧ s (portAt a b q).wire=true
  | .inr _,.inr _ => False

lemma selectedRel_symm {D : Finset Center} (a b : Port (D : Set Center)) (s : Wire → Bool) :
    ∀ ⦃v w : Vertices D⦄, selectedRel a b s v w → selectedRel a b s w v := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      obtain ⟨k,hk,hs⟩ := h
      refine ⟨k,?_,?_⟩
      · rw [←hk,neighbor_neighbor]
      · rw [←hk,incidentWire_neighbor]; exact hs
    | inr q => exact h
  | inr q => cases y <;> exact h

noncomputable def selectedGraph {D : Finset Center} (a b : Port (D : Set Center)) (s : Wire → Bool) :
    SimpleGraph (Vertices D) where
  Adj := selectedRel a b s
  symm := ⟨selectedRel_symm a b s⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl v => obtain ⟨k,hk,_⟩ := h; exact neighbor_ne v.val k hk
    | inr q => exact h⟩

lemma selectedGraph_allowed {D : Finset Center} (a b : Port (D : Set Center)) (s : Wire → Bool) :
    selectedGraph a b s ≤ hardWallGraph D a b := by
  intro x y h
  cases x with
  | inl v => cases y with
    | inl w =>
      exact (adj_iff_neighbor v.val w.val).mpr ⟨h.choose,h.choose_spec.1⟩
    | inr q => cases q <;> exact Subtype.ext h.1
  | inr q => cases y with
    | inl v => cases q <;> exact Subtype.ext h.1
    | inr r => exact False.elim h

lemma selectedGraph_port_neighbors {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) (hs : BoundarySelection a b s) (q : Bool) :
    (selectedGraph a b s).neighborSet (.inr q) = {.inl (portInside (portAt a b q))} := by
  ext x
  cases x with
  | inl v =>
    change (v.val=(portAt a b q).inside ∧ _) ↔ _
    have hq : s (portAt a b q).wire=true := by cases q <;> simp_all [portAt,BoundarySelection]
    simp [hq,portInside,Subtype.ext_iff]
  | inr r => simp [SimpleGraph.neighborSet,selectedGraph,selectedRel]

/-- The neighbor of a center represented by one of its three actual edges. -/
def sideNeighbor {D : Finset Center} (a b : Port (D : Set Center))
    (v : Interior D) (k : Fin 3) : Vertices D → Prop
  | .inl w => neighbor v.val k = w.val
  | .inr q => v.val=(portAt a b q).inside ∧ k=(portAt a b q).side

lemma sideNeighbor_side_unique {D : Finset Center} (a b : Port (D : Set Center))
    (v : Interior D) {k l : Fin 3} {w : Vertices D}
    (hk : sideNeighbor a b v k w) (hl : sideNeighbor a b v l w) : k=l := by
  cases w with
  | inl w => exact neighbor_injective v.val (hk.trans hl.symm)
  | inr q => exact hk.2.trans hl.2.symm

lemma sideNeighbor_neighbor_unique {D : Finset Center} (a b : Port (D : Set Center))
    (hab : a≠b) (v : Interior D) (k : Fin 3) {x y : Vertices D}
    (hx : sideNeighbor a b v k x) (hy : sideNeighbor a b v k y) : x=y := by
  cases x with
  | inl x => cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext (hx.symm.trans hy))
    | inr q =>
      have ho : x.val=(portAt a b q).outside := by rw [←hx,hy.1,hy.2,Port.neighbor_side]
      exact False.elim ((portAt a b q).outside_not_mem (ho ▸ x.property))
  | inr q => cases y with
    | inl y =>
      have ho : y.val=(portAt a b q).outside := by rw [←hy,hx.1,hx.2,Port.neighbor_side]
      exact False.elim ((portAt a b q).outside_not_mem (ho ▸ y.property))
    | inr r =>
      have he : (portAt a b q).wire=(portAt a b r).wire := by
        unfold Port.wire; rw [←hx.1,←hx.2,←hy.1,←hy.2]
      have hp := Port.wire_ext _ _ he
      cases q <;> cases r <;> simp_all [portAt]

lemma selected_side_has_neighbor {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) (hs : BoundarySelection a b s)
    (v : Interior D) (k : Fin 3) (hk : s (incidentWire v.val k)=true) :
    ∃ w : Vertices D, sideNeighbor a b v k w := by
  by_cases hi : neighbor v.val k ∈ D
  · exact ⟨.inl ⟨_,hi⟩,rfl⟩
  · rcases hs.2.2 v.val v.property k hi hk with ha | hb
    · exact ⟨.inr false,by simpa [sideNeighbor,portAt] using a.wire_eq_incident v.property ha⟩
    · exact ⟨.inr true,by simpa [sideNeighbor,portAt] using b.wire_eq_incident v.property hb⟩

lemma sideNeighbor_adj {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) (v : Interior D) (k : Fin 3) (w : Vertices D)
    (hk : s (incidentWire v.val k)=true) (hw : sideNeighbor a b v k w) :
    (selectedGraph a b s).Adj (.inl v) w := by
  cases w with
  | inl w => exact ⟨k,hw,hk⟩
  | inr q =>
    refine ⟨hw.1,?_⟩
    simpa [Port.wire,←hw.1,←hw.2] using hk

lemma adj_sideNeighbor {D : Finset Center} (a b : Port (D : Set Center))
    (s : Wire → Bool) (v : Interior D) (w : Vertices D)
    (h : (selectedGraph a b s).Adj (.inl v) w) :
    ∃ k : Fin 3, s (incidentWire v.val k)=true ∧ sideNeighbor a b v k w := by
  cases w with
  | inl w => obtain ⟨k,hw,hk⟩ := h; exact ⟨k,hk,hw⟩
  | inr q =>
    refine ⟨(portAt a b q).side,?_,h.1,rfl⟩
    simpa [h.1,Port.wire] using h.2

end CriticalHoneycomb.Transfer.FiniteConfigurations

namespace CriticalHoneycomb.Transfer.FiniteConfigurations
open SimpleGraph

/-- Selected geometric sides and selected graph neighbors are in exact
bijection; the hard-wall condition is used only for the missing exterior
neighbors. Distinct ports may share an inside center. -/
noncomputable def centerNeighborEquiv {D : Finset Center} (a b : Port (D : Set Center))
    (hab : a≠b) (s : Wire → Bool) (hs : BoundarySelection a b s) (v : Interior D) :
    {k : Fin 3 // s (incidentWire v.val k)=true} ≃
      (selectedGraph a b s).neighborSet (.inl v) := by
  classical
  let f : {k : Fin 3 // s (incidentWire v.val k)=true} →
      (selectedGraph a b s).neighborSet (.inl v) := fun k =>
    ⟨(selected_side_has_neighbor a b s hs v k.val k.property).choose,
      sideNeighbor_adj a b s v k.val _ k.property
        (selected_side_has_neighbor a b s hs v k.val k.property).choose_spec⟩
  apply Equiv.ofBijective f
  constructor
  · intro k l h
    apply Subtype.ext
    apply sideNeighbor_side_unique a b v
      (selected_side_has_neighbor a b s hs v k.val k.property).choose_spec
    have hval := congrArg Subtype.val h
    change (selected_side_has_neighbor a b s hs v k.val k.property).choose =
      (selected_side_has_neighbor a b s hs v l.val l.property).choose at hval
    rw [hval]
    exact (selected_side_has_neighbor a b s hs v l.val l.property).choose_spec
  · intro w
    obtain ⟨k,hk,hw⟩ := adj_sideNeighbor a b s v w.val w.property
    refine ⟨⟨k,hk⟩,Subtype.ext ?_⟩
    exact sideNeighbor_neighbor_unique a b hab v k
      (selected_side_has_neighbor a b s hs v k hk).choose_spec hw

def selectedSideCount (s : Wire → Bool) (v : Center) : ℕ :=
  (s (incidentWire v 0)).toNat+(s (incidentWire v 1)).toNat+(s (incidentWire v 2)).toNat

lemma selectedSideCount_eq_card (s : Wire → Bool) (v : Center) :
    selectedSideCount s v = Fintype.card {k : Fin 3 // s (incidentWire v k)=true} := by
  classical
  rw [Fintype.card_subtype,Finset.card_filter,Fin.sum_univ_three]
  cases h0 : s (incidentWire v 0) <;> cases h1 : s (incidentWire v 1) <;>
    cases h2 : s (incidentWire v 2) <;>
    simp [selectedSideCount,h0,h1,h2]

lemma selectedGraph_center_degree {D : Finset Center} (a b : Port (D : Set Center))
    (hab : a≠b) (s : Wire → Bool) (hs : BoundarySelection a b s) (v : Interior D) :
    ((selectedGraph a b s).neighborSet (.inl v)).ncard = selectedSideCount s v.val := by
  classical
  change Nat.card ((selectedGraph a b s).neighborSet (.inl v)) = _
  rw [Nat.card_eq_fintype_card,selectedSideCount_eq_card]
  exact (Fintype.card_congr (centerNeighborEquiv a b hab s hs v)).symm

/-- The exact local 0/2 rule, rather than an assumed path partition, gives
an admissible finite configuration on the actual honeycomb graph. -/
noncomputable def configurationOfSides {D : Finset Center} (a b : Port (D : Set Center))
    (hab : a≠b) (s : Wire → Bool) (hs : BoundarySelection a b s)
    (hdeg : ∀ v∈D, selectedSideCount s v=0 ∨ selectedSideCount s v=2) :
    Configuration D a b where
  graph := selectedGraph a b s
  allowed := selectedGraph_allowed a b s
  port_degree := by intro q; rw [selectedGraph_port_neighbors a b s hs q]; simp
  center_degree := by
    intro v
    rw [selectedGraph_center_degree a b hab s hs v]
    exact hdeg v.val v.property

end CriticalHoneycomb.Transfer.FiniteConfigurations


end OAI
