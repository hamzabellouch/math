import OAI.Combinatorics.PlanarL1.Stem

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter
variable {V W : Type} [LinearOrder V] [Finite V] [LinearOrder W] [Finite W]
  [LinearOrder (V⊕W)] {G : SimpleGraph V} {B : Set V}

/-- After processing a frontier vertex, the old remaining ports and all its
new children are the frontier. -/
def starPorts (B : Set V) (v : V) : Set (V⊕W) :=
  {w | Sum.elim (fun u => u∈B ∧ u≠v) (fun _ => True) w}

namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

lemma grow_star (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (hEK : Disjoint (E.region v) K)
    (hsegE : segment ℝ (C.drawing.point v) (target v) ⊆ E.region v)
    (hrad : C.drawing.point v∈segment ℝ C.center (target v))
    (child : W → ℂ) (n : W → ℕ)
    (P : ∀ w, SegmentChain Set.univ (target v) (child w) (n w+1))
    (hP : ∀ w, (P w).IsSimple)
    (hPC : ∀ w, Disjoint (closure C.disk) (P w).trace)
    (hPE : ∀ w u, u∈B → ∀ z∈(P w).trace, z∈E.region u → u=v ∧ z=target v)
    (hPP : ∀ w w', w≠w' → ∀ z∈(P w).trace, z∈(P w').trace → z=target v)
    (hPK : ∀ w, ∀ z∈(P w).trace, z∈K → z=child w)
    (hotherK : ∀ u∈B, ∀ z∈E.region u, z∈K → z=target u) :
    ∃ C' : DiskCore (leafExtension (W := W) G v) (starPorts B v),
    ∃ E' : ExteriorPorts C'.drawing.point (Sum.elim target child) (starPorts B v) C'.disk,
      C'.drawing.point (.inl v)=target v ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈starPorts B v, ∀ z∈E'.region w, z∈K → z=Sum.elim target child w) := by
  classical
  let m (w : W) := target v+(1/2:ℝ)•((P w).vertex 1-target v)
  have hm (w : W) : m w∈segment ℝ (target v) ((P w).vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U (w : W) := ((P w).cutFirst (m w) (hm w)).trace
  have hUsub (w : W) : U w ⊆ (P w).trace := (P w).cutFirst_subset _ _
  have hyU (w : W) : target v∉U w := (P w).cut_avoids_start (hP w) (by norm_num) (by norm_num)
  let F := K ∪ (⋃ w, U w) ∪ ⋃ u : {u // u∈B ∧ u≠v}, E.region u
  have hF : IsClosed F := (hK.union (isClosed_iUnion_of_finite
    (fun w => ((P w).cutFirst _ _).trace_compact.isClosed))).union
    (isClosed_iUnion_of_finite (fun u => (E.compact u u.property.1).isClosed))
  have hdisj : Disjoint (segment ℝ C.center (target v)) F := by
    rw [segment_split hrad]
    apply Disjoint.union_left
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzU
        exact Set.disjoint_left.mp (hPC w) (C.spoke_subset hz) (hUsub w hw)
      · obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.spoke_disjoint C.drawing.point_injective C.convex
          C.isOpen C.center_mem C.port hv u.property.1 (Ne.symm u.property.2)) hz hu
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hEK (hsegE hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzU
        exact hyU w ((hPE w v hv z (hUsub w hw) (hsegE hz)).2 ▸ hw)
      · obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.disjoint v hv u u.property.1 (Ne.symm u.property.2)) (hsegE hz) hu
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hyT : target v∈T := hseg (right_mem_segment ℝ _ _)
  have hxT : C.drawing.point v∈T := hseg hrad
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail (w : W) : Disjoint (closure T) (P w).tail.trace := by
    apply hd.mono_right
    intro z hz
    apply Or.inl; apply Or.inr; apply Set.mem_iUnion.mpr
    refine ⟨w,?_⟩
    change z∈((P w).cutFirst _ _).trace
    rw [(P w).cutFirst_trace]; exact Or.inr hz
  choose q hq hqfr hqne hqny hqin using fun w =>
    (P w).exit_frontier (hP w) hT hTop hyT (htail w)
  let A (w : W) := (P w).cutFirst (q w) (hq w)
  have hAsub (w : W) : (A w).trace ⊆ (P w).trace := (P w).cutFirst_subset _ _
  have hother (u : V) (hu : u∈B) (he : u≠v) : Disjoint (closure T) (E.region u) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨u,hu,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (subset_closure hyT)
    (fun u hu he hz => Set.disjoint_left.mp (hother u hu he) hz (E.start u hu))
    (fun z hz hzS => E.inside v hv z (hsegE hz) hzS)
  let arm (w : W) := segment ℝ (target v) (q w)
  have harm (w : W) : arm w ⊆ (P w).trace :=
    ((convex_segment (target v) ((P w).vertex 1)).segment_subset (left_mem_segment ℝ _ _) (hq w)).trans
      (P w).first_segment_subset
  have harmT (w : W) : arm w ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure (hqfr w))
  have hmeet (w : W) (z : ℂ) (hz : z∈closure C.disk ∪ segment ℝ (C.drawing.point v) (target v))
      (hzP : z∈(P w).trace) : z=target v := by
    rcases hz with hz|hz
    · exact False.elim (Set.disjoint_left.mp (hPC w) hz hzP)
    · exact (hPE w v hv z hzP (hsegE hz)).2
  have hvertex (w : W) (u : V) (hu : Q.point u∈arm w) : u=v :=
    Q.point_injective ((hmeet w _ (hQ.point_control u) (harm w hu)).trans hQ.selected.symm)
  have hcross (w : W) (u x : V) (hux : G.Adj u x) (z : ℂ)
      (hz : z∈arm w) (hz' : z∈Q.region u x) : z=Q.point v := by
    rw [Q.region_eq u x hux] at hz'
    exact (hmeet w z (hQ.trace_control _ hz') (harm w hz)).trans hQ.selected.symm
  obtain ⟨R,hpR,hrR⟩ := Q.attachLeaves v q arm
    (fun w => by rw [hQ.selected]; exact hqny w)
    (fun w => hQ.selected.symm ▸ left_mem_segment ℝ _ _)
    (fun w => right_mem_segment ℝ _ _)
    (fun w => hQ.selected.symm ▸ Relation.ReflTransGen.single Set.Subset.rfl)
    hvertex
    (fun w w' hww z hz hz' => (hPP w w' hww z (harm w hz) (harm w' hz')).trans hQ.selected.symm)
    hcross
  have hpold (u : V) : R.point (.inl u)=Q.point u := congrFun hpR (.inl u)
  have hpnew (w : W) : R.point (.inr w)=q w := congrFun hpR (.inr w)
  let C' : DiskCore (leafExtension (W := W) G v) (starPorts B v) := {
    drawing := R
    disk := T
    center := target v
    convex := hT
    isOpen := hTop
    bounded := hTb
    center_mem := hyT
    point_mem := by
      intro u; cases u with
      | inl u => rw [hpold]; exact hQ.point_mem u
      | inr w => rw [hpnew]; exact frontier_subset_closure (hqfr w)
    trace_mem := by
      intro d z hz
      have hh := hrR d hz
      rcases d with ⟨⟨⟨u,x⟩,hux⟩,hord⟩
      cases u <;> cases x <;> simp only [PLDrawing.starRegion] at hh
      case inl.inl u x =>
        rw [Q.region_eq u x hux] at hh
        exact hQ.trace_mem _ hh
      case inl.inr u w => exact harmT w hh
      case inr.inl w u => exact harmT w hh
      case inr.inr w w' => exact False.elim hh
    port := by
      intro u hu; cases u with
      | inl u => rw [hpold]; exact hQ.on_frontier u hu.1 hu.2
      | inr w => rw [hpnew]; exact hqfr w }
  let E₀ := E.update (PortFrame.ofMove hQ) C.drawing.point_injective C.port hv hother
    isCompact_singleton (show target v∈({target v}:Set ℂ) from rfl)
    (Set.singleton_subset_iff.mpr (E.end_mem v hv))
    (fun z hz _ => hz) (Relation.ReflTransGen.refl)
  have hEold (u : V) (he : u≠v) :
      E₀.region u=segment ℝ (Q.point u) (C.drawing.point u) ∪ E.region u := by
    simp [E₀,ExteriorPorts.update,ExteriorPorts.updatedRegion,he]
  have hEarm (u : V) (hu : u∈B) (he : u≠v) (w : W) :
      Disjoint (E₀.region u) (A w).trace := by
    rw [hEold u he]
    apply Disjoint.union_left
    · exact (hPC w).mono (hQ.tail_old u hu he) (hAsub w)
    · apply Set.disjoint_left.mpr
      intro z hz hz'
      exact he (hPE w u hu z (hAsub w hz') hz).1
  have hyA (w : W) : target v∉(A w).trace := by
    intro hy
    exact hqny w (hqin w _ hy (subset_closure hyT)).symm
  let E' : ExteriorPorts C'.drawing.point (Sum.elim target child) (starPorts B v) C'.disk := {
    region := Sum.elim E₀.region (fun w => (A w).trace)
    compact := by
      intro u hu; cases u with
      | inl u => exact E₀.compact u hu.1
      | inr w => exact (A w).trace_compact
    start := by
      intro u hu; cases u with
      | inl u => change R.point (.inl u)∈E₀.region u; rw [hpold]; exact E₀.start u hu.1
      | inr w => change R.point (.inr w)∈(A w).trace; rw [hpnew]; exact (A w).start_mem_trace
    joined := by
      intro u hu; cases u with
      | inl u => change PolygonallyJoined (E₀.region u) (R.point (.inl u)) (target u)
                 rw [hpold]; exact E₀.joined u hu.1
      | inr w => change PolygonallyJoined (A w).trace (R.point (.inr w)) (child w)
                 rw [hpnew]; exact (A w).joined_trace
    inside := by
      intro u hu z hz hzT; cases u with
      | inl u => change z=R.point (.inl u); rw [hpold]; exact E₀.inside u hu.1 z hz hzT
      | inr w => change z=R.point (.inr w); rw [hpnew]; exact hqin w z hz hzT
    disjoint := by
      intro u hu x hx hux
      cases u with
      | inl u => cases x with
        | inl x => exact E₀.disjoint u hu.1 x hx.1 (fun he => hux (congrArg Sum.inl he))
        | inr w => exact hEarm u hu.1 hu.2 w
      | inr w => cases x with
        | inl u => exact (hEarm u hx.1 hx.2 w).symm
        | inr w' =>
          apply Set.disjoint_left.mpr
          intro z hz hz'
          exact hyA w ((hPP w w' (fun he => hux (congrArg Sum.inr he)) z (hAsub w hz) (hAsub w' hz')) ▸ hz) }
  refine ⟨C',E',(hpold v).trans hQ.selected,hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  intro u hu z hz hzK
  cases u with
  | inl u =>
    change z∈E₀.region u at hz
    rw [hEold u hu.2] at hz
    rcases hz with hz|hz
    · exact False.elim (Set.disjoint_left.mp hCK (hQ.tail_old u hu.1 hu.2 hz) hzK)
    · exact hotherK u hu.1 z hz hzK
  | inr w => exact hPK w z (hAsub w hz) hzK

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma parent_ne {v : V} (hv : v≠T.root) : T.parent v≠v := by
  intro he
  have hh := T.step_depth (show T.Step (T.parent v) v from ⟨hv,rfl⟩)
  rw [he] at hh
  exact lt_irrefl _ hh

lemma step_ne {u v : V} (h : T.Step u v) : u≠v := by
  exact h.2 ▸ T.parent_ne h.1

/-- Vertices already absorbed into the disk form a parent-closed set. -/
def ParentClosed (S : Finset V) : Prop := ∀ v∈S, T.parent v∈S

def Frontier (S : Finset V) (v : V) : Prop := v∉S ∧ T.parent v∈S

def Scope (S : Finset V) (v : V) : Prop := v∈S ∨ T.Frontier S v

lemma frontier_ne_root {S : Finset V} {v : V} (hv : T.Frontier S v) : v≠T.root := by
  intro he; subst v
  exact hv.1 (T.at_root ▸ hv.2)

lemma scope_parent {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Scope S v) : T.parent v∈S := by
  exact hv.elim (hS v) And.right

lemma frontier_neighbor {S : Finset V} (hS : T.ParentClosed S) {v u : V}
    (hv : T.Frontier S v) (hu : T.Scope S u) (hvu : T.graph.Adj v u) : u=T.parent v := by
  rcases hvu with h|h
  · exact False.elim (hv.1 (h.2.symm ▸ T.scope_parent hS hu))
  · exact h.2

lemma frontier_leaf {S : Finset V} (hS : T.ParentClosed S) {v : {v // T.Scope S v}}
    (hv : T.Frontier S v.val) (u u' : {v // T.Scope S v})
    (hu : (SimpleGraph.comap Subtype.val T.graph).Adj v u)
    (hu' : (SimpleGraph.comap Subtype.val T.graph).Adj v u') : u=u' := by
  exact Subtype.ext ((T.frontier_neighbor hS hv u.property hu).trans
    (T.frontier_neighbor hS hv u'.property hu').symm)

lemma child_out {S : Finset V} (hS : T.ParentClosed S) {v w : V}
    (hv : T.Frontier S v) (hw : T.Step v w) : ¬T.Scope S w := by
  intro h
  exact hv.1 (hw.2.symm ▸ T.scope_parent hS h)

variable [DecidableEq V]

lemma insert_closed {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    T.ParentClosed (insert v S) := by
  classical
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact Finset.mem_insert_of_mem hv.2
  · exact Finset.mem_insert_of_mem (hS w hw)

lemma frontier_insert {S : Finset V} (hS : T.ParentClosed S) {v w : V} (hv : T.Frontier S v) :
    T.Frontier (insert v S) w ↔ (T.Frontier S w ∧ w≠v) ∨ T.Step v w := by
  classical
  simp only [Frontier,Finset.mem_insert,not_or] at *
  constructor
  · rintro ⟨⟨hwv,hwS⟩,hp⟩
    rcases hp with hp|hp
    · exact Or.inr ⟨fun he => by subst w; rw [T.at_root] at hp; exact hwv hp,hp.symm⟩
    · exact Or.inl ⟨⟨hwS,hp⟩,hwv⟩
  · rintro (⟨⟨hwS,hp⟩,hwv⟩|hw)
    · exact ⟨⟨hwv,hwS⟩,Or.inr hp⟩
    · exact ⟨⟨Ne.symm (T.step_ne hw),fun hwS =>
        hv.1 (hw.2.symm ▸ hS w hwS)⟩,Or.inl hw.2.symm⟩

lemma scope_insert {S : Finset V} (hS : T.ParentClosed S) {v w : V} (hv : T.Frontier S v) :
    T.Scope (insert v S) w ↔ T.Scope S w ∨ T.Step v w := by
  classical
  rw [Scope,T.frontier_insert hS hv]
  constructor
  · rintro (h|h)
    · rcases Finset.mem_insert.mp h with rfl|h
      · exact Or.inl (Or.inr hv)
      · exact Or.inl (Or.inl h)
    · exact h.elim (fun h => Or.inl (Or.inr h.1)) Or.inr
  · rintro (h|h)
    · rcases h with h|h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · by_cases he : w=v
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl he))
        · exact Or.inr (Or.inl ⟨h,he⟩)
    · exact Or.inr (Or.inr h)

omit [DecidableEq V] in
lemma old_child_adj {S : Finset V} (hS : T.ParentClosed S) {v u w : V}
    (hv : T.Frontier S v) (hu : T.Scope S u) (hw : T.Step v w) :
    T.graph.Adj u w ↔ u=v := by
  constructor
  · rintro (h|h)
    · exact h.2.trans hw.2.symm
    · exact False.elim (T.child_out hS hv hw (Or.inl (h.2 ▸ T.scope_parent hS hu)))
  · intro he; subst u; exact Or.inl hw

omit [DecidableEq V] in
lemma children_not_adj {v u w : V} (hu : T.Step v u) (hw : T.Step v w) :
    ¬T.graph.Adj u w := by
  rintro (h|h)
  · exact T.step_ne hu (h.2.trans hw.2.symm).symm
  · exact T.step_ne hw (h.2.trans hu.2.symm).symm

noncomputable def extensionMap {S : Finset V} (v : V) :
    ({u // T.Scope S u} ⊕ {w // T.Step v w}) → V := Sum.elim Subtype.val Subtype.val

omit [DecidableEq V] in
lemma extensionMap_injective {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    Function.Injective (T.extensionMap (S := S) v) := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b =>
      change a.val=b.val at he
      exact False.elim (T.child_out hS hv b.property (he ▸ a.property))
  | inr a => cases b with
    | inl b =>
      change a.val=b.val at he
      exact False.elim (T.child_out hS hv a.property (he.symm ▸ b.property))
    | inr b => exact congrArg Sum.inr (Subtype.ext he)

noncomputable def extensionEquiv {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    ({u // T.Scope S u} ⊕ {w // T.Step v w}) ≃ {u // T.Scope (insert v S) u} :=
  Equiv.ofBijective (fun a => ⟨T.extensionMap v a,by
    apply (T.scope_insert hS hv).mpr
    cases a with
    | inl a => exact Or.inl a.property
    | inr a => exact Or.inr a.property⟩) ⟨
    fun a b h => T.extensionMap_injective hS hv (congrArg Subtype.val h),by
      intro a
      rcases (T.scope_insert hS hv).mp a.property with h|h
      · exact ⟨.inl ⟨a.val,h⟩,rfl⟩
      · exact ⟨.inr ⟨a.val,h⟩,rfl⟩⟩

lemma extension_graph {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    Topology.leafExtension (W := {w // T.Step v w})
      (SimpleGraph.comap Subtype.val T.graph) (⟨v,Or.inr hv⟩:{u // T.Scope S u}) =
    SimpleGraph.comap (T.extensionEquiv hS hv)
      (SimpleGraph.comap Subtype.val T.graph) := by
  ext a b
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b =>
      change (a=⟨v,Or.inr hv⟩) ↔ T.graph.Adj a.val b.val
      rw [T.old_child_adj hS hv a.property b.property]
      exact Subtype.ext_iff
  | inr a => cases b with
    | inl b =>
      change (b=⟨v,Or.inr hv⟩) ↔ T.graph.Adj a.val b.val
      rw [T.graph.adj_comm,T.old_child_adj hS hv b.property a.property]
      exact Subtype.ext_iff
    | inr b =>
      exact iff_false_intro (T.children_not_adj a.property b.property) |>.symm

lemma extension_ports {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v)
    (a : {u // T.Scope S u} ⊕ {w // T.Step v w}) :
    a∈Topology.starPorts {w : {u // T.Scope S u} | T.Frontier S w.val} ⟨v,Or.inr hv⟩ ↔
      T.Frontier (insert v S) (T.extensionEquiv hS hv a).val := by
  rw [T.frontier_insert hS hv]
  cases a with
  | inl a =>
    change (T.Frontier S a.val ∧ a≠⟨v,Or.inr hv⟩) ↔
      (T.Frontier S a.val ∧ a.val≠v) ∨ T.Step v a.val
    have ha : ¬T.Step v a.val := fun h => T.child_out hS hv h a.property
    simp only [ha,or_false,ne_eq,Subtype.ext_iff]
  | inr a =>
    exact iff_true_intro (Or.inr a.property) |>.symm

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {V W : Type} [LinearOrder V] [LinearOrder W]
  {G : SimpleGraph V} {H : SimpleGraph W}

lemma PLDrawing.pullback (P : PLDrawing G) (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v)) :
    ∃ Q : PLDrawing H, Q.point=P.point ∘ f ∧
      ∀ d, (Q.chain d).trace ⊆ P.region (f d.val.fst) (f d.val.snd) := by
  apply PLDrawing.ofSymmetricRegions (P.point ∘ f) (P.point_injective.comp hf)
    (fun u v => P.region (f u) (f v))
  · intro u v h; exact P.region_start _ _ (hG u v h)
  · intro u v h; exact P.region_joined _ _ (hG u v h)
  · intro u v h w hw
    exact (P.region_vertex _ _ (hG u v h) _ hw).elim (fun he => Or.inl (hf he)) (fun he => Or.inr (hf he))
  · intro u v w x h h' hne z hz hz'
    exact P.region_intersect _ _ _ _ (hG u v h) (hG w x h')
      (fun he => hne (he.elim (fun h => Or.inl ⟨hf h.1,hf h.2⟩)
        (fun h => Or.inr ⟨hf h.1,hf h.2⟩))) hz hz'

noncomputable def ExteriorPorts.retarget {p t : V → ℂ} {B : Set V} {S : Set ℂ}
    (E : ExteriorPorts p t B S) (t' : V → ℂ) (ht : ∀ w, t w=t' w) :
    ExteriorPorts p t' B S := {
  region := E.region
  compact := E.compact
  start := E.start
  joined := fun w hw => by rw [← ht w]; exact E.joined w hw
  inside := E.inside
  disjoint := E.disjoint }

namespace DiskCore
variable {B : Set V} (C : DiskCore G B) {target : V → ℂ}

lemma region_mem (u v : V) (h : G.Adj u v) : C.drawing.region u v ⊆ closure C.disk := by
  rw [C.drawing.region_eq u v h]
  exact C.trace_mem _

/-- Relabel an actual core and all exterior paths along an injective graph map.
No drawing or disk existence is assumed beyond the supplied core. -/
lemma pullback (E : ExteriorPorts C.drawing.point target B C.disk)
    (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v))
    {B' : Set W} (hB : ∀ w∈B', f w∈B) :
    ∃ C' : DiskCore H B', ∃ E' : ExteriorPorts C'.drawing.point (target ∘ f) B' C'.disk,
      C'.disk=C.disk ∧ (∀ w, C'.drawing.point w=C.drawing.point (f w)) ∧
      (∀ w, E'.region w=E.region (f w)) := by
  obtain ⟨Q,hQ,hsub⟩ := C.drawing.pullback f hf hG
  let C' : DiskCore H B' := ⟨Q,C.disk,C.center,C.convex,C.isOpen,C.bounded,C.center_mem,
    (fun w => by rw [hQ]; exact C.point_mem (f w)),
    (fun d => (hsub d).trans (C.region_mem _ _ (hG _ _ d.val.adj))),
    (fun w hw => by rw [hQ]; exact C.port (f w) (hB w hw))⟩
  let E' : ExteriorPorts C'.drawing.point (target ∘ f) B' C'.disk := {
    region := fun w => E.region (f w)
    compact := fun w hw => E.compact (f w) (hB w hw)
    start := fun w hw => by change Q.point w∈_; rw [hQ]; exact E.start (f w) (hB w hw)
    joined := fun w hw => by change PolygonallyJoined _ (Q.point w) _; rw [hQ]; exact E.joined (f w) (hB w hw)
    inside := fun w hw z hz hz' => by
      change z=Q.point w; rw [hQ]; exact E.inside (f w) (hB w hw) z hz hz'
    disjoint := fun w hw u hu hne => E.disjoint (f w) (hB w hw) (f u) (hB u hu) (hf.ne hne) }
  exact ⟨C',E',rfl,(fun w => congrFun hQ w),fun _ => rfl⟩

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology.PLDrawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

def carrier (S : Set V) : Set ℂ :=
  (⋃ v : S, {P.point v.val}) ∪ ⋃ u : S, ⋃ v : S, P.region u.val v.val

lemma point_mem_carrier {S : Set V} {v : V} (hv : v∈S) : P.point v∈P.carrier S :=
  Or.inl (mem_iUnion.mpr ⟨⟨v,hv⟩,rfl⟩)

lemma region_mem_carrier {S : Set V} {u v : V} (hu : u∈S) (hv : v∈S) :
    P.region u v ⊆ P.carrier S := fun _ hz =>
  Or.inr (mem_iUnion.mpr ⟨⟨u,hu⟩,mem_iUnion.mpr ⟨⟨v,hv⟩,hz⟩⟩)

lemma carrier_mono {S T : Set V} (h : S ⊆ T) : P.carrier S ⊆ P.carrier T := by
  rintro z (hz|hz)
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    rcases hv with rfl
    exact P.point_mem_carrier (h v.property)
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    exact P.region_mem_carrier (h u.property) (h v.property) hv

lemma carrier_compact [Finite V] (S : Set V) : IsCompact (P.carrier S) :=
  (isCompact_iUnion (fun _ => isCompact_singleton)).union
    (isCompact_iUnion (fun u => isCompact_iUnion (fun v => P.region_compact u.val v.val)))

lemma region_adj {u v : V} {z : ℂ} (hz : z∈P.region u v) : G.Adj u v := by
  classical
  by_contra h
  simp [region,h] at hz

lemma point_carrier_iff {S : Set V} {v : V} : P.point v∈P.carrier S ↔ v∈S := by
  constructor
  · rintro (hz|hz)
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hz
      exact P.point_injective (mem_singleton_iff.mp hw) ▸ w.property
    · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
      obtain ⟨w,hw⟩ := mem_iUnion.mp hu
      exact (P.region_vertex _ _ (P.region_adj hw) v hw).elim
        (fun he => he ▸ u.property) (fun he => he ▸ w.property)
  · exact P.point_mem_carrier

lemma region_carrier_intersection {S : Set V} {u v : V} (h : G.Adj u v)
    (hu : u∉S) {z : ℂ} (hz : z∈P.region u v) (hzS : z∈P.carrier S) :
    z=P.point v := by
  rcases hzS with hzS|hzS
  · obtain ⟨w,hw⟩ := mem_iUnion.mp hzS
    have he := mem_singleton_iff.mp hw
    rw [he] at hz
    rcases P.region_vertex _ _ h w.val hz with he'|he'
    · exact False.elim (hu (he' ▸ w.property))
    · exact he.trans (congrArg P.point he')
  · obtain ⟨w,hw⟩ := mem_iUnion.mp hzS
    obtain ⟨x,hx⟩ := mem_iUnion.mp hw
    have hne : ¬((u=w.val ∧ v=x.val) ∨ (u=x.val ∧ v=w.val)) := by
      rintro (he|he)
      · exact hu (he.1.symm ▸ w.property)
      · exact hu (he.1.symm ▸ x.property)
    rcases (P.region_intersect _ _ _ _ h (P.region_adj hx) hne hz hx).1 with he|he
    · have : P.point u∈P.carrier S := by rw [← he]; exact P.region_mem_carrier w.property x.property hx
      exact False.elim (hu ((P.point_carrier_iff).mp this))
    · exact he

lemma carrier_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (P.carrier S) (P.carrier T) := by
  rw [disjoint_left]
  intro z hz hz'
  rcases hz with hz|hz
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    rw [mem_singleton_iff.mp hv] at hz'
    exact disjoint_left.mp h v.property (P.point_carrier_iff.mp hz')
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    have he := P.region_carrier_intersection (P.region_adj hv)
      (fun hu => disjoint_left.mp h u.property hu) hv hz'
    rw [he] at hz'
    exact disjoint_left.mp h v.property (P.point_carrier_iff.mp hz')

lemma region_simple_chain {u v : V} (h : G.Adj u v) :
    ∃ n : ℕ, ∃ C : SegmentChain Set.univ (P.point u) (P.point v) (n+1),
      C.IsSimple ∧ C.trace ⊆ P.region u v := by
  obtain ⟨n,C,hC⟩ := (P.region_joined u v h).exists_simple_segmentChain
  cases n with
  | zero => exact False.elim (h.ne (P.point_injective (C.start.symm.trans C.finish)))
  | succ n => exact ⟨n,C.mapSet (subset_univ _),C.mapSet_simple _ hC,
      C.trace_subset (P.region_start u v h)⟩

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

/-- The raw unprocessed drawing is a fixed closed obstacle at each stage. -/
def outside (S : Finset V) : Set ℂ := P.carrier {v | v∉S}

lemma outside_closed (S : Finset V) : IsClosed (outside P S) :=
  (P.carrier_compact _).isClosed

omit [Fintype V] in
lemma outside_insert_subset (S : Finset V) (v : V) :
    outside P (insert v S) ⊆ outside P S :=
  P.carrier_mono (fun _ h => fun hw => h (Finset.mem_insert_of_mem hw))

omit [Fintype V] in
lemma point_outside_iff (S : Finset V) (v : V) : P.point v∈outside P S ↔ v∉S :=
  P.point_carrier_iff

/-- A partially swallowed tree, retaining real residual stems to the original
frontier vertices in the supplied polygonal drawing. -/
structure Growth (S : Finset V) where
  core : DiskCore (SimpleGraph.comap Subtype.val T.graph)
    {w : {w // T.Scope S w} | T.Frontier S w.val}
  stems : ExteriorPorts core.drawing.point (fun w => P.point w.val)
    {w : {w // T.Scope S w} | T.Frontier S w.val} core.disk
  avoid : Disjoint (closure core.disk) (outside P S)
  contact : ∀ w, T.Frontier S w.val → ∀ z∈stems.region w,
    z∈outside P S → z=P.point w.val

namespace Growth
variable {T P}

lemma advance {S : Finset V} (hS : T.ParentClosed S) (H : T.Growth P S)
    (hG : T.graph ≤ G) {v : V} (hv : T.Frontier S v) :
    Nonempty (T.Growth P (insert v S)) := by
  classical
  let A := {u // T.Scope S u}
  let W := {w // T.Step v w}
  let a : A := ⟨v,Or.inr hv⟩
  let e := T.extensionEquiv hS hv
  let : LinearOrder (A⊕W) := LinearOrder.lift' e e.injective
  have hleaf : ∀ w : A, T.Frontier S w.val → ∀ u u',
      (SimpleGraph.comap Subtype.val T.graph).Adj w u →
      (SimpleGraph.comap Subtype.val T.graph).Adj w u' → u=u' :=
    fun _ hw _ _ h h' => T.frontier_leaf hS hw _ _ h h'
  have htK : P.point v∈outside P S := (point_outside_iff P S v).mpr hv.1
  obtain ⟨C,E,hseg,hrad,hCK,hprotect⟩ := H.core.prepare_stem H.stems hleaf
    (v := a) hv (outside_closed P S) H.avoid htK (H.contact a hv)
  have hcontact (u : A) (hu : T.Frontier S u.val) (z : ℂ) (hz : z∈E.region u)
      (hzK : z∈outside P S) : z=P.point u.val :=
    H.contact u hu z (hprotect u hu z hz hzK) hzK
  have hCK' : Disjoint (closure C.disk) (outside P (insert v S)) :=
    hCK.mono_right (outside_insert_subset P S v)
  have hvn : P.point v∉outside P (insert v S) := by
    rw [point_outside_iff]; simp
  have hEK' : Disjoint (E.region a) (outside P (insert v S)) := by
    rw [disjoint_left]; intro z hz hzK
    exact hvn (hcontact a hv z hz (outside_insert_subset P S v hzK) ▸ hzK)
  have he (w : W) : G.Adj v w.val := hG (Or.inl w.property)
  choose n Q hQ hsub using fun w : W => P.region_simple_chain (he w)
  have hout (w : W) : (Q w).trace ⊆ outside P S :=
    (hsub w).trans (P.region_mem_carrier hv.1 (fun hw =>
      T.child_out hS hv w.property (Or.inl hw)))
  have hPC (w : W) : Disjoint (closure C.disk) (Q w).trace := hCK.mono_right (hout w)
  have hPE (w : W) (u : A) (hu : T.Frontier S u.val) (z : ℂ)
      (hz : z∈(Q w).trace) (hzE : z∈E.region u) : u=a ∧ z=P.point v := by
    have hz' := hcontact u hu z hzE (hout w hz)
    have hmem : P.point u.val∈P.region v w.val := hz' ▸ hsub w hz
    rcases P.region_vertex _ _ (he w) u.val hmem with hu'|hu'
    · exact ⟨Subtype.ext hu',hz'.trans (congrArg P.point hu')⟩
    · exact False.elim (T.child_out hS hv w.property (hu' ▸ u.property))
  have hPP (w w' : W) (hne : w≠w') (z : ℂ)
      (hz : z∈(Q w).trace) (hz' : z∈(Q w').trace) : z=P.point v := by
    have hne' : ¬((v=v ∧ w.val=w'.val) ∨ (v=w'.val ∧ w.val=v)) := by
      rintro (hh|hh)
      · exact hne (Subtype.ext hh.2)
      · exact (he w).ne hh.2.symm
    rcases (P.region_intersect _ _ _ _ (he w) (he w') hne' (hsub w hz) (hsub w' hz')).1 with hh|hh
    · exact hh
    · have hm : P.point w.val∈P.region v w'.val := hh ▸ hsub w' hz'
      rcases P.region_vertex _ _ (he w') w.val hm with hh'|hh'
      · exact (he w).ne hh'.symm |>.elim
      · exact hne (Subtype.ext hh') |>.elim
  have hPK (w : W) (z : ℂ) (hz : z∈(Q w).trace)
      (hzK : z∈outside P (insert v S)) : z=P.point w.val :=
    P.region_carrier_intersection (he w) (by simp) (hsub w hz) hzK
  obtain ⟨C₁,E₁,hselected,havoid,hcontact₁⟩ := C.grow_star E hleaf hv
    (outside_closed P (insert v S)) hCK' hEK' hseg hrad (fun w : W => P.point w.val)
    n Q hQ hPC hPE hPP hPK
    (fun u hu z hz hzK => hcontact u hu z hz (outside_insert_subset P S v hzK))
  have hgraph : ∀ u u', (SimpleGraph.comap Subtype.val T.graph).Adj u u' →
      (leafExtension (W := W) (SimpleGraph.comap Subtype.val T.graph) a).Adj (e.symm u) (e.symm u') := by
    intro u u' h
    rw [T.extension_graph hS hv]
    change T.graph.Adj (e (e.symm u)).val (e (e.symm u')).val
    change T.graph.Adj u.val u'.val at h
    simpa only [Equiv.apply_symm_apply] using h
  have hports : ∀ w : {u // T.Scope (insert v S) u}, T.Frontier (insert v S) w.val →
      e.symm w∈starPorts {u : A | T.Frontier S u.val} a := by
    intro w hw
    apply (T.extension_ports hS hv (e.symm w)).mpr
    change T.Frontier (insert v S) (e (e.symm w)).val
    simpa only [Equiv.apply_symm_apply] using hw
  obtain ⟨C₂,E₂,hD,hp,hE⟩ := C₁.pullback E₁ e.symm e.symm.injective hgraph hports
  have htarget (w : {u // T.Scope (insert v S) u}) :
      (Sum.elim (fun u : A => P.point u.val) (fun u : W => P.point u.val) ∘ e.symm) w=P.point w.val := by
    have heq := congrArg Subtype.val (e.apply_symm_apply w)
    change T.extensionMap v (e.symm w)=w.val at heq
    have hm : Sum.elim (fun u : A => P.point u.val) (fun u : W => P.point u.val) (e.symm w)=
        P.point (T.extensionMap v (e.symm w)) := by cases e.symm w <;> rfl
    exact hm.trans (congrArg P.point heq)
  let E₃ := E₂.retarget (fun w => P.point w.val) htarget
  refine ⟨⟨C₂,E₃,?_,?_⟩⟩
  · rw [hD]; exact havoid
  · intro w hw z hz hzK
    have hz' : z∈E₁.region (e.symm w) := (hE w) ▸ hz
    exact (hcontact₁ (e.symm w) (hports w hw) z hz' hzK).trans (htarget w)

end Growth
end PlanarL1.HeightTree




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma singleton_closed : T.ParentClosed {T.root} := by
  intro v hv
  have he : v=T.root := Finset.mem_singleton.mp hv
  subst v
  simpa only [T.at_root] using Finset.mem_singleton_self T.root

lemma frontier_root_iff (v : V) : T.Frontier {T.root} v ↔ T.Step T.root v := by
  simp only [Frontier,Finset.mem_singleton,Step]
  exact and_congr_right (fun _ => eq_comm)

lemma scope_root_iff (v : V) : T.Scope {T.root} v ↔ v=T.root ∨ T.Step T.root v := by
  rw [Scope,T.frontier_root_iff]
  simp only [Finset.mem_singleton]

noncomputable def rootMap : PUnit ⊕ {w // T.Step T.root w} → V := Sum.elim (fun _ => T.root) Subtype.val

lemma rootMap_injective : Function.Injective T.rootMap := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b => exact False.elim (b.property.1 he.symm)
  | inr a => cases b with
    | inl b => exact False.elim (a.property.1 he)
    | inr b => exact congrArg Sum.inr (Subtype.ext he)

noncomputable def rootEquiv : (PUnit ⊕ {w // T.Step T.root w}) ≃ {w // T.Scope {T.root} w} :=
  Equiv.ofBijective (fun a => ⟨T.rootMap a,by
    apply (T.scope_root_iff _).mpr
    cases a with
    | inl a => exact Or.inl rfl
    | inr a => exact Or.inr a.property⟩) ⟨
    fun a b h => T.rootMap_injective (congrArg Subtype.val h),by
      intro a
      rcases (T.scope_root_iff _).mp a.property with h|h
      · exact ⟨.inl PUnit.unit,Subtype.ext h.symm⟩
      · exact ⟨.inr ⟨a.val,h⟩,rfl⟩⟩

lemma root_graph :
    PlanarL1.Topology.leafExtension (W := {w // T.Step T.root w}) (⊥ : SimpleGraph PUnit) PUnit.unit =
    SimpleGraph.comap T.rootEquiv (SimpleGraph.comap Subtype.val T.graph) := by
  classical
  ext a b
  cases a with
  | inl a => cases b with
    | inl b => exact iff_false_intro (fun h : T.graph.Adj T.root T.root => h.ne rfl) |>.symm
    | inr b =>
      change a=PUnit.unit ↔ T.graph.Adj T.root b.val
      exact ⟨fun _ => Or.inl b.property,fun _ => Subsingleton.elim _ _⟩
  | inr a => cases b with
    | inl b =>
      change b=PUnit.unit ↔ T.graph.Adj a.val T.root
      exact ⟨fun _ => Or.inr a.property,fun _ => Subsingleton.elim _ _⟩
    | inr b => exact iff_false_intro (T.children_not_adj a.property b.property) |>.symm

lemma root_ports (a : PUnit ⊕ {w // T.Step T.root w}) :
    a.isRight ↔ T.Frontier {T.root} (T.rootEquiv a).val := by
  rw [T.frontier_root_iff]
  cases a with
  | inl a =>
    change (false=true) ↔ T.Step T.root T.root
    simp only [Bool.false_eq_true,false_iff]
    exact fun h => h.1 rfl
  | inr a =>
    change (true=true) ↔ T.Step T.root a.val
    exact ⟨fun _ => a.property,fun _ => rfl⟩

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {W : Type} [LinearOrder W] [Finite W] [LinearOrder (PUnit⊕W)]

noncomputable def singletonDrawing (y : ℂ) : PLDrawing (⊥ : SimpleGraph PUnit) where
  point := fun _ => y
  point_injective := fun _ _ _ => Subsingleton.elim _ _
  count := fun d => False.elim d.val.adj
  chain := fun d => False.elim d.val.adj
  simple := fun d => False.elim d.val.adj
  on_vertex := fun d => False.elim d.val.adj
  intersect := fun d => False.elim d.val.adj

/-- The first enclosing disk cuts each outgoing polygonal arm once, leaving
its entire residual trace outside. -/
lemma star_core (y : ℂ) (child : W → ℂ) (n : W → ℕ)
    (P : ∀ w, SegmentChain Set.univ y (child w) (n w+1))
    (hP : ∀ w, (P w).IsSimple)
    (hPP : ∀ w w', w≠w' → ∀ z∈(P w).trace, z∈(P w').trace → z=y)
    {K : Set ℂ} (hK : IsClosed K) (hyK : y∉K)
    (hPK : ∀ w, ∀ z∈(P w).trace, z∈K → z=child w) :
    ∃ C : DiskCore (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit)
        {w | w.isRight},
    ∃ E : ExteriorPorts C.drawing.point (Sum.elim (fun _ => y) child) {w | w.isRight} C.disk,
      C.drawing.point (.inl PUnit.unit)=y ∧ Disjoint (closure C.disk) K ∧
      (∀ w, w.isRight → ∀ z∈E.region w, z∈K → z=Sum.elim (fun _ : PUnit => y) child w) := by
  classical
  let m (w : W) := y+(1/2:ℝ)•((P w).vertex 1-y)
  have hm (w : W) : m w∈segment ℝ y ((P w).vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U (w : W) := ((P w).cutFirst (m w) (hm w)).trace
  have hyU (w : W) : y∉U w := (P w).cut_avoids_start (hP w) (by norm_num) (by norm_num)
  let F := K ∪ ⋃ w, U w
  have hF : IsClosed F := hK.union (isClosed_iUnion_of_finite
    (fun w => ((P w).cutFirst _ _).trace_compact.isClosed))
  have hyF : y∉F := by
    rintro (h|h)
    · exact hyK h
    · obtain ⟨w,hw⟩ := mem_iUnion.mp h; exact hyU w hw
  have hdis : Disjoint (segment ℝ y y) F := by simpa only [segment_same] using disjoint_singleton_left.mpr hyF
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdis
  have hyT : y∈T := hseg (left_mem_segment ℝ _ _)
  have htail (w : W) : Disjoint (closure T) (P w).tail.trace := by
    apply hd.mono_right
    intro z hz
    apply Or.inr; apply mem_iUnion.mpr; refine ⟨w,?_⟩
    change z∈((P w).cutFirst _ _).trace
    rw [(P w).cutFirst_trace]; exact Or.inr hz
  choose q hq hqfr hqne hqny hqin using fun w =>
    (P w).exit_frontier (hP w) hT hTop hyT (htail w)
  let A (w : W) := (P w).cutFirst (q w) (hq w)
  have hAsub (w : W) : (A w).trace ⊆ (P w).trace := (P w).cutFirst_subset _ _
  let arm (w : W) := segment ℝ y (q w)
  have harm (w : W) : arm w ⊆ (P w).trace :=
    ((convex_segment y ((P w).vertex 1)).segment_subset (left_mem_segment ℝ _ _) (hq w)).trans
      (P w).first_segment_subset
  have harmT (w : W) : arm w ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure (hqfr w))
  let Q₀ := singletonDrawing y
  obtain ⟨Q,hQ,htrace⟩ := Q₀.attachLeaves PUnit.unit q arm hqny
    (fun w => left_mem_segment ℝ _ _) (fun w => right_mem_segment ℝ _ _)
    (fun w => Relation.ReflTransGen.single (by exact subset_rfl))
    (fun _ _ _ => Subsingleton.elim _ _)
    (fun w w' h z hz hz' => hPP w w' h z (harm w hz) (harm w' hz'))
    (fun _ _ _ h => False.elim h)
  let C : DiskCore (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit) {w | w.isRight} := {
    drawing := Q
    disk := T
    center := y
    convex := hT
    isOpen := hTop
    bounded := hTb
    center_mem := hyT
    point_mem := by
      intro w; rw [hQ]; cases w with
      | inl w => exact subset_closure hyT
      | inr w => exact frontier_subset_closure (hqfr w)
    trace_mem := by
      intro d z hz
      have hh := htrace d hz
      cases ha : d.val.fst with
      | inl a => cases hb : d.val.snd with
        | inl b => have h := d.val.adj; rw [ha,hb] at h; exact False.elim h
        | inr b => rw [ha,hb] at hh; exact harmT b hh
      | inr a => cases hb : d.val.snd with
        | inl b => rw [ha,hb] at hh; exact harmT a hh
        | inr b => have h := d.val.adj; rw [ha,hb] at h; exact False.elim h
    port := by
      intro w hw; cases w with
      | inl w => simp at hw
      | inr w => rw [hQ]; exact hqfr w }
  let E : ExteriorPorts C.drawing.point (Sum.elim (fun _ => y) child) {w | w.isRight} C.disk := {
    region := Sum.elim (fun _ => ∅) (fun w => (A w).trace)
    compact := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => exact (A w).trace_compact
    start := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => change Q.point (.inr w)∈_; rw [hQ]; exact (A w).start_mem_trace
    joined := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => change PolygonallyJoined _ (Q.point (.inr w)) _; rw [hQ]; exact (A w).joined_trace
    inside := by intro w hw z hz hz'; cases w with
      | inl w => simp at hw
      | inr w => change z=Q.point (.inr w); rw [hQ]; exact hqin w z hz hz'
    disjoint := by
      intro w hw w' hw' hne
      cases w with
      | inl w => simp at hw
      | inr w => cases w' with
        | inl w' => simp at hw'
        | inr w' =>
          apply disjoint_left.mpr
          intro z hz hz'
          have he := hPP w w' (fun he => hne (congrArg Sum.inr he)) z (hAsub w hz) (hAsub w' hz')
          have he' := hqin w z hz (he.symm ▸ subset_closure hyT)
          exact hqny w (he'.symm.trans he) }
  refine ⟨C,E,?_,hd.mono_right subset_union_left,?_⟩
  · change Q.point (.inl PUnit.unit)=y; rw [hQ]; rfl
  · intro w hw z hz hzK
    cases w with
    | inl w => simp at hw
    | inr w => exact hPK w z (hAsub w hz) hzK

end PlanarL1.Topology




namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

lemma initial_growth (hG : T.graph ≤ G) : Nonempty (T.Growth P {T.root}) := by
  classical
  let W := {w // T.Step T.root w}
  let e := T.rootEquiv
  let : LinearOrder (PUnit⊕W) := LinearOrder.lift' e e.injective
  have he (w : W) : G.Adj T.root w.val := hG (Or.inl w.property)
  choose n Q hQ hsub using fun w : W => P.region_simple_chain (he w)
  have hPP (w w' : W) (hne : w≠w') (z : ℂ)
      (hz : z∈(Q w).trace) (hz' : z∈(Q w').trace) : z=P.point T.root := by
    have hne' : ¬((T.root=T.root ∧ w.val=w'.val) ∨ (T.root=w'.val ∧ w.val=T.root)) := by
      rintro (hh|hh)
      · exact hne (Subtype.ext hh.2)
      · exact (he w).ne hh.2.symm
    rcases (P.region_intersect _ _ _ _ (he w) (he w') hne' (hsub w hz) (hsub w' hz')).1 with hh|hh
    · exact hh
    · have hm : P.point w.val∈P.region T.root w'.val := hh ▸ hsub w' hz'
      rcases P.region_vertex _ _ (he w') w.val hm with hh'|hh'
      · exact (he w).ne hh'.symm |>.elim
      · exact hne (Subtype.ext hh') |>.elim
  have hyK : P.point T.root∉outside P {T.root} := by rw [point_outside_iff]; simp
  have hPK (w : W) (z : ℂ) (hz : z∈(Q w).trace)
      (hzK : z∈outside P {T.root}) : z=P.point w.val :=
    P.region_carrier_intersection (he w) (by simp) (hsub w hz) hzK
  obtain ⟨C,E,hroot,havoid,hcontact⟩ := star_core (P.point T.root) (fun w : W => P.point w.val)
    n Q hQ hPP (outside_closed P {T.root}) hyK hPK
  have hgraph : ∀ u u', (SimpleGraph.comap Subtype.val T.graph).Adj u u' →
      (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit).Adj (e.symm u) (e.symm u') := by
    intro u u' h
    rw [T.root_graph]
    change T.graph.Adj (e (e.symm u)).val (e (e.symm u')).val
    change T.graph.Adj u.val u'.val at h
    simpa only [Equiv.apply_symm_apply] using h
  have hports : ∀ w : {u // T.Scope {T.root} u}, T.Frontier {T.root} w.val →
      (e.symm w).isRight := by
    intro w hw
    apply (T.root_ports (e.symm w)).mpr
    change T.Frontier {T.root} (e (e.symm w)).val
    simpa only [Equiv.apply_symm_apply] using hw
  obtain ⟨C₂,E₂,hD,hp,hE⟩ := C.pullback E e.symm e.symm.injective hgraph hports
  have htarget (w : {u // T.Scope {T.root} u}) :
      (Sum.elim (fun _ : PUnit => P.point T.root) (fun u : W => P.point u.val) ∘ e.symm) w=P.point w.val := by
    have heq := congrArg Subtype.val (e.apply_symm_apply w)
    change T.rootMap (e.symm w)=w.val at heq
    have hm : Sum.elim (fun _ : PUnit => P.point T.root) (fun u : W => P.point u.val) (e.symm w)=
        P.point (T.rootMap (e.symm w)) := by cases e.symm w <;> rfl
    exact hm.trans (congrArg P.point heq)
  let E₃ := E₂.retarget (fun w => P.point w.val) htarget
  refine ⟨⟨C₂,E₃,?_,?_⟩⟩
  · rw [hD]; exact havoid
  · intro w hw z hz hzK
    have hz' : z∈E.region (e.symm w) := (hE w) ▸ hz
    exact (hcontact (e.symm w) (hports w hw) z hz' hzK).trans (htarget w)

end PlanarL1.HeightTree



end

end OAI
