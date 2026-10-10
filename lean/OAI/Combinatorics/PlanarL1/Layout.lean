import OAI.Combinatorics.PlanarL1.Growth

namespace OAI

section



namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

lemma growth_exists (hG : T.graph ≤ G) (S : Finset V)
    (hroot : T.root∈S) (hS : T.ParentClosed S) : Nonempty (T.Growth P S) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S={T.root}
    · subst S; exact T.initial_growth P hG
    have hne : (S.erase T.root).Nonempty := by
      by_contra hh
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hh
      apply hs
      exact (Finset.insert_erase hroot).symm.trans (by rw [hempty]; rfl)
    obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image (S.erase T.root) T.depth hne
    have hvr : v≠T.root := (Finset.mem_erase.mp hv).1
    have hvS : v∈S := (Finset.mem_erase.mp hv).2
    have hroot' : T.root∈S.erase v := Finset.mem_erase.mpr ⟨hvr.symm,hroot⟩
    have hS' : T.ParentClosed (S.erase v) := by
      intro w hw
      have hwv := (Finset.mem_erase.mp hw).1
      have hwS := (Finset.mem_erase.mp hw).2
      refine Finset.mem_erase.mpr ⟨?_,hS w hwS⟩
      intro he
      by_cases hwr : w=T.root
      · subst w; exact hvr (he.symm.trans T.at_root)
      · have hd := T.step_depth (show T.Step v w from ⟨hwr,he.symm⟩)
        exact (not_lt_of_ge (hmax w (Finset.mem_erase.mpr ⟨hwr,hwS⟩))) hd
    have hfront : T.Frontier (S.erase v) v := by
      refine ⟨(by simp),Finset.mem_erase.mpr ⟨T.parent_ne hvr,hS v hvS⟩⟩
    obtain ⟨H⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) hroot' hS'
    simpa only [Finset.insert_erase hvS] using H.advance hS' hG hfront

noncomputable def internal : Finset V := Finset.univ.filter (fun v => ¬T.IsLeaf v)

omit [LinearOrder V] in
lemma mem_internal (v : V) : v∈T.internal ↔ ¬T.IsLeaf v := by simp [internal]

lemma internal_closed : T.ParentClosed T.internal := by
  intro v hv
  by_cases he : v=T.root
  · subst v; rwa [T.at_root]
  · apply (T.mem_internal _).mpr
    exact fun h => h v ⟨he,rfl⟩

omit [LinearOrder V] in
lemma internal_scope (hroot : ¬T.IsLeaf T.root) (v : V) : T.Scope T.internal v := by
  by_cases h : T.IsLeaf v
  · refine Or.inr ⟨fun hv => (T.mem_internal v).mp hv h,(T.mem_internal _).mpr ?_⟩
    have hvr : v≠T.root := fun he => hroot (he ▸ h)
    exact fun hh => hh v ⟨hvr,rfl⟩
  · exact Or.inl ((T.mem_internal _).mpr h)

omit [LinearOrder V] in
lemma internal_frontier (hroot : ¬T.IsLeaf T.root) (v : V) :
    T.Frontier T.internal v ↔ T.IsLeaf v := by
  constructor
  · intro h
    by_contra hh
    exact h.1 ((T.mem_internal _).mpr hh)
  · intro h
    rcases T.internal_scope hroot v with hv|hv
    · exact False.elim ((T.mem_internal _).mp hv h)
    · exact hv

/-- Every actual polygonally drawn finite tree can be enclosed in a convex disk,
with the leaf stubs left as disjoint exterior polygonal arcs. All untouched raw
leaf-to-leaf drawing pieces remain outside the closed disk. -/
lemma tree_core (hG : T.graph ≤ G) (hroot : ¬T.IsLeaf T.root) :
    ∃ C : DiskCore T.graph {v | T.IsLeaf v},
      ∃ E : ExteriorPorts C.drawing.point P.point {v | T.IsLeaf v} C.disk,
        Disjoint (closure C.disk) (P.carrier {v | T.IsLeaf v}) ∧
        ∀ v, T.IsLeaf v → ∀ z∈E.region v, z∈P.carrier {v | T.IsLeaf v} → z=P.point v := by
  classical
  obtain ⟨H⟩ := T.growth_exists P hG T.internal ((T.mem_internal _).mpr hroot) T.internal_closed
  let i : V → {v // T.Scope T.internal v} := fun v => ⟨v,T.internal_scope hroot v⟩
  have hi : Function.Injective i := fun _ _ h => congrArg Subtype.val h
  have hgraph : ∀ u v, T.graph.Adj u v →
      (SimpleGraph.comap Subtype.val T.graph).Adj (i u) (i v) := fun _ _ h => h
  have hports : ∀ v, T.IsLeaf v → T.Frontier T.internal (i v).val :=
    fun v h => (T.internal_frontier hroot v).mpr h
  obtain ⟨C,E,hD,hp,hE⟩ := H.core.pullback H.stems i hi hgraph hports
  have hout : outside P T.internal=P.carrier {v | T.IsLeaf v} := by
    unfold outside
    congr 1
    ext v
    simp only [mem_ofPred_eq,T.mem_internal,not_not]
  refine ⟨C,E,?_,?_⟩
  · rw [hD,← hout]; exact H.avoid
  · intro v hv z hz hzK
    apply H.contact (i v) (hports v hv) z
    · exact (hE v) ▸ hz
    · rwa [hout]

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set

lemma PolygonallyJoined.exists_path {S : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoined S x y) (hx : x∈S) :
    ∃ p : Path x y, range p ⊆ S := by
  induction h with
  | refl => exact ⟨Path.refl x,by rintro z ⟨t,rfl⟩; exact hx⟩
  | @tail y z h hz ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨p.trans (Path.segment y z),by rw [Path.trans_range,Path.range_segment]; exact union_subset hp hz⟩

namespace DiskCore
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} {B : Set V} (C : DiskCore G B)

lemma carrier_subset (S : Set V) : C.drawing.carrier S ⊆ closure C.disk := by
  intro z hz
  rcases hz with hz|hz
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    exact mem_singleton_iff.mp hv ▸ C.point_mem v.val
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    exact C.region_mem _ _ (C.drawing.region_adj hv) hv

end DiskCore
end PlanarL1.Topology

namespace PlanarL1.HeightTree
open Set PlanarL1.Topology Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [LinearOrder V] (T : HeightTree V)

lemma ancestor_plpath (P : PLDrawing T.graph) {u v : V} (h : T.Ancestor u v)
    {S : Set V} (hS : ∀ w, T.Ancestor u w → T.Ancestor w v → w∈S) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier S := by
  induction h with
  | refl => exact ⟨Path.refl _,by rintro z ⟨t,rfl⟩; exact P.point_mem_carrier (hS _ .refl .refl)⟩
  | @tail v w huv hvw ih =>
    obtain ⟨p,hp⟩ := ih (fun a ha hb => hS a ha (hb.tail hvw))
    obtain ⟨q,hq⟩ := (P.region_joined v w (Or.inl hvw)).exists_path (P.region_start v w (Or.inl hvw))
    refine ⟨p.trans q,?_⟩
    rw [Path.trans_range]
    exact union_subset hp (hq.trans (P.region_mem_carrier (hS v huv (.single hvw))
      (hS w (huv.tail hvw) .refl)))

lemma descendants_pljoined (P : PLDrawing T.graph) (a : V) {u v : V}
    (hu : T.Ancestor a u) (hv : T.Ancestor a v) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier {w | T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_plpath P hu (fun _ h _ => h)
  obtain ⟨q,hq⟩ := T.ancestor_plpath P hv (fun _ h _ => h)
  exact ⟨p.symm.trans q,by rw [Path.trans_range,Path.symm_range]; exact union_subset hp hq⟩

lemma nondescendants_pljoined (P : PLDrawing T.graph) (a : V) {u v : V}
    (hu : ¬T.Ancestor a u) (hv : ¬T.Ancestor a v) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier {w | ¬T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_plpath P (T.root_ancestor u)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hu (ha.trans h))
  obtain ⟨q,hq⟩ := T.ancestor_plpath P (T.root_ancestor v)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hv (ha.trans h))
  exact ⟨p.symm.trans q,by rw [Path.trans_range,Path.symm_range]; exact union_subset hp hq⟩

lemma core_prefix_connected {B : Set V} {n : ℕ} (C : DiskCore T.graph B)
    (h : ℂ ≃ₜ ℂ) (hbound : ∀ z∈closure C.disk, ‖h z‖≤1)
    (leaf : Fin n → V) (angle : Fin n → ℝ)
    (hend : ∀ i, h (C.drawing.point (leaf i))=(Circle.exp (angle i) : ℂ))
    (horder : StrictMono angle) (hspan : ∀ i j, angle j-angle i<2*π)
    (a : V) {i j : Fin n} (hi : T.Ancestor a (leaf i)) (hj : T.Ancestor a (leaf j)) :
    (T.prefixGraph leaf a).Reachable i j := by
  apply Columns.consecutive_connected (T.prefixGraph leaf a) {k | T.Ancestor a (leaf k)}
    (fun _ _ hne hc ha hb => ⟨hne,hc,ha,hb⟩) _ hi hj
  intro w x y z hwx hxy hyz hbad
  suffices impossible : ∀ (S U : Set V), Disjoint S U →
      (∃ p : Path (C.drawing.point (leaf w)) (C.drawing.point (leaf y)), range p⊆C.drawing.carrier S) →
      (∃ q : Path (C.drawing.point (leaf x)) (C.drawing.point (leaf z)), range q⊆C.drawing.carrier U) → False by
    rcases hbad with ⟨hw,hx,hy,hz⟩ | ⟨hw,hx,hy,hz⟩
    · exact impossible {v | T.Ancestor a v} {v | ¬T.Ancestor a v}
        disjoint_compl_right (T.descendants_pljoined C.drawing a hw hy)
        (T.nondescendants_pljoined C.drawing a hx hz)
    · exact impossible {v | ¬T.Ancestor a v} {v | T.Ancestor a v}
        disjoint_compl_left (T.nondescendants_pljoined C.drawing a hw hy)
        (T.descendants_pljoined C.drawing a hx hz)
  intro S U hdis ⟨p,hp⟩ ⟨q,hq⟩
  let p' := (p.map h.continuous).cast (hend w).symm (hend y).symm
  let q' := (q.map h.continuous).cast (hend x).symm (hend z).symm
  obtain ⟨s,t,hst⟩ := Topology.disk_cyclic_arcs_meet (angle w) (angle x) (angle y) (angle z)
    (horder hwx) (horder hxy) (horder hyz) (by linarith [hspan w z]) p' q'
    (fun t => hbound _ (C.carrier_subset S (hp (mem_range_self t))))
    (fun t => hbound _ (C.carrier_subset U (hq (mem_range_self t))))
  have he : p s=q t := h.injective hst
  exact disjoint_left.mp (C.drawing.carrier_disjoint hdis) (hp (mem_range_self s))
    (he ▸ hq (mem_range_self t))

lemma layout_of_core [Fintype V] (C : DiskCore T.graph {v | T.IsLeaf v})
    (P : SimpleGraph {v : V // T.IsLeaf v})
    (hheight : ∀ i j, P.Adj i j → T.height i.val=T.height j.val)
    (hmatch : ∀ i j k, P.Adj i j → P.Adj i k → j=k)
    (arc : ∀ i j, P.Adj i j → Path (C.drawing.point i.val) (C.drawing.point j.val))
    (hout : ∀ i j h t, arc i j h t∉C.disk)
    (hdis : ∀ i j h k l h', i≠k → i≠l → j≠k → j≠l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    ∃ (L : T.Layout (Fintype.card {v : V // T.IsLeaf v})),
      ∀ i j, L.pair.Adj i j ↔ P.Adj ⟨L.leaf i,L.isLeaf i⟩ ⟨L.leaf j,L.isLeaf j⟩ := by
  classical
  obtain ⟨h,hi,hcl,hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall C.convex
    (show (interior C.disk).Nonempty by rw [C.isOpen.interior_eq]; exact ⟨C.center,C.center_mem⟩) C.bounded
  have hnorm (v : {v : V // T.IsLeaf v}) : ‖h (C.drawing.point v.val)‖=1 := by
    have hm := mem_image_of_mem h (C.port v.val v.property)
    rw [hfr] at hm
    simpa only [Metric.mem_sphere,dist_zero_right] using hm
  have hbound (z : ℂ) (hz : z∈closure C.disk) : ‖h z‖≤1 := by
    have hm := mem_image_of_mem h hz
    rw [hcl] at hm
    simpa only [Metric.mem_closedBall,dist_zero_right] using hm
  have hexterior (z : ℂ) (hz : z∉C.disk) : 1≤‖h z‖ := by
    by_contra! hn
    have hm : h z∈Metric.ball (0:ℂ) 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hn
    rw [← hi] at hm
    obtain ⟨w,hw,he⟩ := hm
    exact hz (h.injective he ▸ interior_subset hw)
  obtain ⟨e,he,hspan⟩ := Topology.finite_port_order (fun v : {v : V // T.IsLeaf v} => h (C.drawing.point v.val))
    hnorm (h.injective.comp (C.drawing.point_injective.comp Subtype.val_injective))
  let angle (i : Fin (Fintype.card {v : V // T.IsLeaf v})) := Complex.arg (h (C.drawing.point (e i).val))
  have hend i : h (C.drawing.point (e i).val)=(Circle.exp (angle i) : ℂ) :=
    (Topology.circle_exp_arg (hnorm (e i))).symm
  let A : ∀ i j, (SimpleGraph.comap e P).Adj i j →
      Path (Circle.exp (angle i) : ℂ) (Circle.exp (angle j) : ℂ) :=
    fun i j hij => ((arc (e i) (e j) hij).map h.continuous).cast (hend i).symm (hend j).symm
  have hnc : ColumnOrder.Noncrossing (SimpleGraph.comap e P) := by
    apply Topology.noncrossing_of_exterior_arcs _ angle he hspan A
    · intro i j hij t; exact hexterior _ (hout (e i) (e j) hij t)
    · intro i j hij k l hkl hik hil hjk hjl
      rw [disjoint_left]
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      have hh : h (arc (e i) (e j) hij s)=h (arc (e k) (e l) hkl t) := hs.trans ht.symm
      exact disjoint_left.mp (hdis (e i) (e j) hij (e k) (e l) hkl
        (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
        (mem_range_self s) (h.injective hh ▸ mem_range_self t)
  let L : T.Layout (Fintype.card {v : V // T.IsLeaf v}) := {
    leaf := fun i => (e i).val
    isLeaf := fun i => (e i).property
    injective := Subtype.val_injective.comp e.injective
    covers := fun v hv => ⟨e.symm ⟨v,hv⟩,by simp⟩
    prefix_connected := fun a i j hi hj =>
      T.core_prefix_connected C h hbound _ angle hend he hspan a hi hj
    pair := SimpleGraph.comap e P
    noncrossing := hnc
    paired_height := fun i j hij => hheight (e i) (e j) hij
    matching := fun i j k hij hik => e.injective (hmatch (e i) (e j) (e k) hij hik) }
  exact ⟨L,fun _ _ => Iff.rfl⟩

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)
  {p : V → ℂ} {B : Set V} {D : Set ℂ} (E : ExteriorPorts p P.point B D)

/-- The untouched raw carrier together with the actual exterior stubs. -/
def stemCarrier (S : Set V) : Set ℂ := P.carrier S ∪ ⋃ v : S, E.region v.val

lemma stemCarrier_disjoint
    (hcontact : ∀ v∈B, ∀ z∈E.region v, z∈P.carrier B → z=P.point v)
    {S U : Set V} (hS : S⊆B) (hU : U⊆B) (hSU : Disjoint S U) :
    Disjoint (stemCarrier P E S) (stemCarrier P E U) := by
  have cross {S U : Set V} (hS : S⊆B) (hU : U⊆B) (hSU : Disjoint S U) :
      Disjoint (P.carrier S) (⋃ v : U, E.region v.val) := by
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨v,hv⟩ := mem_iUnion.mp hz'
    have he := hcontact v.val (hU v.property) z hv (P.carrier_mono hS hz)
    exact disjoint_left.mp hSU (P.point_carrier_iff.mp (he ▸ hz)) v.property
  apply Disjoint.union_left
  · exact Disjoint.union_right (P.carrier_disjoint hSU) (cross hS hU hSU)
  · apply Disjoint.union_right (cross hU hS hSU.symm).symm
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    obtain ⟨w,hw⟩ := mem_iUnion.mp hz'
    exact disjoint_left.mp (E.disjoint v.val (hS v.property) w.val (hU w.property)
      (fun he => disjoint_left.mp hSU v.property (he ▸ w.property))) hv hw

end PlanarL1.Topology

namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

/-- The literal planar leaf layout is constructed from a real raw drawing of
its tree and terminal matching. Neither a contour order nor a disk is assumed. -/
lemma layout_of_drawing (P : PLDrawing G) (hG : T.graph ≤ G) (hroot : ¬T.IsLeaf T.root)
    (M : SimpleGraph {v : V // T.IsLeaf v})
    (hMG : ∀ i j, M.Adj i j → G.Adj i.val j.val)
    (hheight : ∀ i j, M.Adj i j → T.height i.val=T.height j.val)
    (hmatch : ∀ i j k, M.Adj i j → M.Adj i k → j=k) :
    ∃ (L : T.Layout (Fintype.card {v : V // T.IsLeaf v})),
      ∀ i j, L.pair.Adj i j ↔ M.Adj ⟨L.leaf i,L.isLeaf i⟩ ⟨L.leaf j,L.isLeaf j⟩ := by
  classical
  obtain ⟨C,E,havoid,hcontact⟩ := T.tree_core P hG hroot
  choose s hs using fun v : {v // T.IsLeaf v} =>
    (E.joined v.val v.property).exists_path (E.start v.val v.property)
  choose r hr using fun i j (h : M.Adj i j) =>
    (P.region_joined i.val j.val (hMG i j h)).exists_path (P.region_start i.val j.val (hMG i j h))
  let A : ∀ i j, M.Adj i j → Path (C.drawing.point i.val) (C.drawing.point j.val) :=
    fun i j h => ((s i).trans (r i j h)).trans (s j).symm
  have hS (i j : {v // T.IsLeaf v}) : ({i.val,j.val} : Set V) ⊆ {v | T.IsLeaf v} := by
    intro v hv
    rcases hv with rfl|hv
    · exact i.property
    · rw [mem_singleton_iff] at hv; exact hv ▸ j.property
  have hArange (i j : {v // T.IsLeaf v}) (h : M.Adj i j) :
      range (A i j h) ⊆ stemCarrier P E {i.val,j.val} := by
    change range (((s i).trans (r i j h)).trans (s j).symm) ⊆ _
    rw [Path.trans_range,Path.trans_range,Path.symm_range]
    refine union_subset (union_subset ?_ ?_) ?_
    · intro z hz; exact Or.inr (mem_iUnion.mpr ⟨⟨i.val,by simp⟩,hs i hz⟩)
    · intro z hz; exact Or.inl (P.region_mem_carrier (by simp) (by simp) (hr i j h hz))
    · intro z hz; exact Or.inr (mem_iUnion.mpr ⟨⟨j.val,by simp⟩,hs j hz⟩)
  have houtside (S : Set V) (hS : S⊆{v | T.IsLeaf v}) (z : ℂ)
      (hz : z∈stemCarrier P E S) : z∉C.disk := by
    intro hzD
    rcases hz with hz|hz
    · exact disjoint_left.mp havoid (subset_closure hzD) (P.carrier_mono hS hz)
    · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
      have he := E.inside v.val (hS v.property) z hv (subset_closure hzD)
      have hf := C.port v.val (hS v.property)
      have hn : C.drawing.point v.val∉interior C.disk := hf.2
      exact hn (by rw [C.isOpen.interior_eq]; exact he ▸ hzD)
  apply T.layout_of_core C M hheight hmatch A
  · intro i j h t; exact houtside _ (hS i j) _ (hArange i j h (mem_range_self t))
  · intro i j h k l h' hik hil hjk hjl
    have hSU : Disjoint ({i.val,j.val} : Set V) {k.val,l.val} := by
      simp only [disjoint_left,mem_insert_iff,mem_singleton_iff]
      intro v hv hv'
      rcases hv with rfl|rfl <;> rcases hv' with he|he
      · exact hik (Subtype.ext he)
      · exact hil (Subtype.ext he)
      · exact hjk (Subtype.ext he)
      · exact hjl (Subtype.ext he)
    exact (stemCarrier_disjoint P E hcontact (hS i j) (hS k l) hSU).mono
      (hArange i j h) (hArange k l h')

end PlanarL1.HeightTree




namespace PlanarL1.Topology.Drawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)

lemma forward_interior_meet (d e : ForwardDart G) {s t : unitInterval}
    (hs : 0<(s:ℝ)) (hs' : (s:ℝ)<1) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1)
    (he : D.edge d.val.fst d.val.snd d.val.adj s=D.edge e.val.fst e.val.snd e.val.adj t) :
    d=e ∧ s=t := by
  have hd := ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ s t hs hs' ht ht' he)
  subst e
  exact ⟨rfl,D.edge_injective _ _ _ he⟩

namespace Split
attribute [local instance] Classical.propDecidable
variable (S : Set (ForwardDart G))

abbrev Tip := S × Fin 2
abbrev Node := V ⊕ Tip S
abbrev Piece := {d : ForwardDart G // d∉S} ⊕ (S × Fin 3)

noncomputable def tipTime (k : Fin 2) : unitInterval := ⟨((k.val:ℝ)+1)/3,by
  constructor
  · positivity
  · have hk : (k.val:ℝ)<2 := by exact_mod_cast k.isLt
    linarith⟩

lemma tipTime_pos (k : Fin 2) : 0<(tipTime k:ℝ) := by dsimp [tipTime]; positivity
lemma tipTime_lt_one (k : Fin 2) : (tipTime k:ℝ)<1 := by
  have hk : (k.val:ℝ)<2 := by exact_mod_cast k.isLt
  dsimp [tipTime]; linarith

noncomputable def point : Node S → ℂ
  | .inl v => D.point v
  | .inr (d,k) => D.edge d.val.val.fst d.val.val.snd d.val.val.adj (tipTime k)

lemma point_injective : Function.Injective (point D S) := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (D.point_injective he)
    | inr b => exact False.elim (D.interior_avoid _ _ _ _ a (tipTime_pos b.2) (tipTime_lt_one b.2) he.symm)
  | inr a => cases b with
    | inl b => exact False.elim (D.interior_avoid _ _ _ _ b (tipTime_pos a.2) (tipTime_lt_one a.2) he)
    | inr b =>
      obtain ⟨hd,ht⟩ := D.forward_interior_meet a.1.val b.1.val
        (tipTime_pos a.2) (tipTime_lt_one a.2) (tipTime_pos b.2) (tipTime_lt_one b.2) he
      have hk : a.2=b.2 := by
        apply Fin.ext
        have hh := congrArg Subtype.val ht
        change ((a.2.val:ℝ)+1)/3=((b.2.val:ℝ)+1)/3 at hh
        exact_mod_cast (show (a.2.val:ℝ)=(b.2.val:ℝ) by linarith)
      exact congrArg Sum.inr (Prod.ext (Subtype.ext hd) hk)

def meshNode (d : S) (r : Fin 4) : Node S :=
  if h0 : r.val=0 then .inl d.val.val.fst
  else if h3 : r.val=3 then .inl d.val.val.snd
  else .inr (d,⟨r.val-1,by omega⟩)

noncomputable def meshTime (r : Fin 4) : unitInterval := ⟨(r.val:ℝ)/3,by
  constructor
  · positivity
  · have hr : (r.val:ℝ)<4 := by exact_mod_cast r.isLt
    have hr' : r.val≤3 := by omega
    have hr'' : (r.val:ℝ)≤3 := by exact_mod_cast hr'
    linarith⟩

lemma mesh_point (d : S) (r : Fin 4) :
    point D S (meshNode S d r)=D.edge d.val.val.fst d.val.val.snd d.val.val.adj (meshTime r) := by
  fin_cases r <;> norm_num [meshNode,point,meshTime,tipTime]

noncomputable def label : Piece S → ForwardDart G
  | .inl d => d.val
  | .inr (d,_) => d.val

def src : Piece S → Node S
  | .inl d => .inl d.val.val.fst
  | .inr (d,k) => meshNode S d k.castSucc

def dst : Piece S → Node S
  | .inl d => .inl d.val.val.snd
  | .inr (d,k) => meshNode S d k.succ

noncomputable def first : Piece S → unitInterval
  | .inl _ => 0
  | .inr (_,k) => meshTime k.castSucc

noncomputable def last : Piece S → unitInterval
  | .inl _ => 1
  | .inr (_,k) => meshTime k.succ

lemma first_lt_last (p : Piece S) : (first S p:ℝ)<(last S p:ℝ) := by
  cases p with
  | inl p => exact zero_lt_one
  | inr p => dsimp [first,last,meshTime]; push_cast; linarith

lemma src_point (p : Piece S) :
    point D S (src S p)=D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj (first S p) := by
  cases p with
  | inl p => exact (Path.source _).symm
  | inr p => exact mesh_point D S p.1 p.2.castSucc

lemma dst_point (p : Piece S) :
    point D S (dst S p)=D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj (last S p) := by
  cases p with
  | inl p => exact (Path.target _).symm
  | inr p => exact mesh_point D S p.1 p.2.succ

lemma src_ne_dst (D : Drawing G) (p : Piece S) : src S p≠dst S p := by
  intro he
  have hp := congrArg (point D S) he
  rw [src_point,dst_point] at hp
  have ht := congrArg Subtype.val (D.edge_injective _ _ _ hp)
  exact (ne_of_lt (first_lt_last S p)) ht

lemma interior_point_avoid (p : Piece S) {t : unitInterval}
    (ht₀ : (first S p:ℝ)<(t:ℝ)) (ht₁ : (t:ℝ)<(last S p:ℝ)) (v : Node S) :
    D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj t≠point D S v := by
  have ht : 0<(t:ℝ) := lt_of_le_of_lt (first S p).property.1 ht₀
  have ht' : (t:ℝ)<1 := lt_of_lt_of_le ht₁ (last S p).property.2
  intro he
  cases v with
  | inl v => exact D.interior_avoid _ _ _ t v ht ht' he
  | inr v =>
    obtain ⟨hd,htt⟩ := D.forward_interior_meet (label S p) v.1.val ht ht'
      (tipTime_pos v.2) (tipTime_lt_one v.2) he
    cases p with
    | inl p =>
      change p.val=v.1.val at hd
      exact p.property (hd.symm ▸ v.1.property)
    | inr p =>
      rw [htt] at ht₀ ht₁
      change (p.2.val:ℝ)/3 < ((v.2.val:ℝ)+1)/3 at ht₀
      change ((v.2.val:ℝ)+1)/3 < ((p.2.val+1:ℕ):ℝ)/3 at ht₁
      have hlo : p.2.val<v.2.val+1 := by exact_mod_cast (show (p.2.val:ℝ)<(v.2.val:ℝ)+1 by linarith)
      have hhi : v.2.val+1<p.2.val+1 := by
        exact_mod_cast (show (v.2.val:ℝ)+1<(p.2.val:ℝ)+1 by push_cast at ht₁; linarith)
      omega

lemma interior_piece_unique (p q : Piece S) {s t : unitInterval}
    (hs₀ : (first S p:ℝ)<(s:ℝ)) (hs₁ : (s:ℝ)<(last S p:ℝ))
    (ht₀ : (first S q:ℝ)<(t:ℝ)) (ht₁ : (t:ℝ)<(last S q:ℝ))
    (he : D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj s=
      D.edge (label S q).val.fst (label S q).val.snd (label S q).val.adj t) : p=q := by
  obtain ⟨hd,hst⟩ := D.forward_interior_meet (label S p) (label S q)
    (lt_of_le_of_lt (first S p).property.1 hs₀) (lt_of_lt_of_le hs₁ (last S p).property.2)
    (lt_of_le_of_lt (first S q).property.1 ht₀) (lt_of_lt_of_le ht₁ (last S q).property.2) he
  subst t
  cases p with
  | inl p => cases q with
    | inl q => exact congrArg Sum.inl (Subtype.ext hd)
    | inr q =>
      change p.val=q.1.val at hd
      exact False.elim (p.property (hd.symm ▸ q.1.property))
  | inr p => cases q with
    | inl q =>
      change p.1.val=q.val at hd
      exact False.elim (q.property (hd ▸ p.1.property))
    | inr q =>
      have hk : p.2=q.2 := by
        apply Fin.ext
        change (p.2.val:ℝ)/3 < (s:ℝ) at hs₀
        change (s:ℝ)<((p.2.val+1:ℕ):ℝ)/3 at hs₁
        change (q.2.val:ℝ)/3 < (s:ℝ) at ht₀
        change (s:ℝ)<((q.2.val+1:ℕ):ℝ)/3 at ht₁
        push_cast at hs₁ ht₁
        have hpq : p.2.val<q.2.val+1 := by exact_mod_cast (show (p.2.val:ℝ)<(q.2.val:ℝ)+1 by linarith)
        have hqp : q.2.val<p.2.val+1 := by exact_mod_cast (show (q.2.val:ℝ)<(p.2.val:ℝ)+1 by linarith)
        omega
      exact congrArg Sum.inr (Prod.ext (Subtype.ext hd) hk)

end Split
end PlanarL1.Topology.Drawing



end

end OAI
