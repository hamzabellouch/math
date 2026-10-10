import OAI.Probability.CriticalZ3.Peierls

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Coarse
abbrev Point := PlanarBoundary.Point
abbrev Direction := PlanarBoundary.Direction
abbrev outward := PlanarBoundary.outward

def center (r : ℕ) (v : Point) : Vertex := ![(20*(r:ℤ)+1)*v.1,(20*(r:ℤ)+1)*v.2,0]
def Q (r : ℕ) (v : Point) : Box := Box.cube (center r v) (10*r)
def B (r : ℕ) (v : Point) : Box := Box.cube (center r v) (4*r)
def PairRegion (r : ℕ) (v x : Point) : Set Vertex := {y | (Q r v).Contains y ∨ (Q r x).Contains y}

@[simp] theorem center_zero (r : ℕ) : center r 0 = 0 := by ext i; fin_cases i <;> simp [center]

theorem cube_unique (r : ℕ) {v w : Point} {x : Vertex}
    (hv : (Q r v).Contains x) (hw : (Q r w).Contains x) : v = w := by
  have hg (a b t : ℤ) (h0 : (20*(r:ℤ)+1)*a-(10*r:ℕ) ≤ t)
      (h1 : t ≤ (20*(r:ℤ)+1)*a+(10*r:ℕ))
      (h2 : (20*(r:ℤ)+1)*b-(10*r:ℕ) ≤ t)
      (h3 : t ≤ (20*(r:ℤ)+1)*b+(10*r:ℕ)) : a = b := by
    push_cast at h0 h1 h2 h3
    have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
    by_contra h
    rcases lt_or_gt_of_ne h with hh|hh
    · have : a+1 ≤ b := by omega
      nlinarith
    · have : b+1 ≤ a := by omega
      nlinarith
  apply Prod.ext
  · exact hg v.1 w.1 (x 0) (hv 0).1 (hv 0).2 (hw 0).1 (hw 0).2
  · exact hg v.2 w.2 (x 1) (hv 1).1 (hv 1).2 (hw 1).1 (hw 1).2

theorem Q_disjoint (r : ℕ) {v w : Point} (h : v ≠ w) : Disjoint (Q r v).vertices (Q r w).vertices := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (cube_unique r ((Box.mem_vertices _ _).mp hx) ((Box.mem_vertices _ _).mp hy))

theorem B_subset_Q (r : ℕ) (v : Point) : ∀ x, (B r v).Contains x → (Q r v).Contains x := by
  intro x hx
  apply Box.contains_cube_iff.mpr
  exact cube_mono (center r v) (by omega) (Box.contains_cube_iff.mp hx)

theorem zero_in_Q (r : ℕ) : (Q r 0).Contains 0 := by
  rw [Q,center_zero]
  exact Box.center_mem_cube _ _

theorem zero_outside_pair (r : ℕ) {v w : Point} (hv : v ≠ 0) (hw : w ≠ 0) :
    (0:Vertex) ∉ PairRegion r v w := by
  rintro (h|h)
  · exact hv (cube_unique r h (zero_in_Q r))
  · exact hw (cube_unique r h (zero_in_Q r))

noncomputable def interface (r : ℕ) (v w : Point) : Finset Bond :=
  (((Q r v).vertices ∪ (Q r w).vertices) ×ˢ Finset.univ).filter
    (fun e => ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)))

@[simp] theorem mem_interface (r : ℕ) (v w : Point) (e : Bond) : e ∈ interface r v w ↔
    ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)) := by
  simp only [interface,Finset.mem_filter,Finset.mem_product,Finset.mem_union,
    Box.mem_vertices,Finset.mem_univ,and_true]
  exact ⟨fun h => h.2,fun h => ⟨h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),h⟩⟩

theorem interface_comm (r : ℕ) (v w : Point) : interface r v w = interface r w v := by
  ext e
  simp only [mem_interface,or_comm]

theorem interface_eq_endpoints (r : ℕ) {v w a b : Point} {e : Bond}
    (h : e ∈ interface r v w) (h' : e ∈ interface r a b) :
    (v = a ∧ w = b) ∨ (v = b ∧ w = a) := by
  rw [mem_interface] at h h'
  rcases h with h|h <;> rcases h' with h'|h'
  · exact Or.inl ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩
  · exact Or.inl ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩

theorem internal_not_interface (r : ℕ) {u v w : Point} (hvw : v ≠ w) :
    Disjoint (Q r u).bonds (interface r v w) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hi
  have hh := (Box.mem_bonds _ _).mp he
  rw [mem_interface] at hi
  rcases hi with hi|hi
  · exact hvw ((cube_unique r hi.1 hh.1).trans (cube_unique r hh.2 hi.2))
  · exact hvw ((cube_unique r hi.2 hh.2).trans (cube_unique r hh.1 hi.1))

theorem internal_pair_bond (r : ℕ) (v w : Point) (e : Bond) :
    Model.Internal .bond (PairRegion r v w) e ↔
      e ∈ (Q r v).bonds ∪ (Q r w).bonds ∪ interface r v w := by
  simp only [Model.Internal,PairRegion,Set.mem_ofPred_eq,Finset.mem_union,Box.mem_bonds,mem_interface]
  tauto

def frame (r : ℕ) (v : Point) (d : Direction) : SignedSymmetry where
  perm := if d = 0 ∨ d = 2 then Equiv.swap 0 1 else Equiv.refl _
  signs := fun i => if d = 0 then decide (i ≠ 1) else if d = 3 then decide (i ≠ 0) else true
  shift := center r v

@[simp] theorem frame_zero (r : ℕ) (v : Point) (d : Direction) : (frame r v d).vertex 0 = center r v := by
  ext i
  simp [frame,SignedSymmetry.vertex]

@[simp] theorem frame_next (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex (LatticeRelay.axisCenter (20*(r:ℤ)+1)) = center r (v+outward d) := by
  ext i
  fin_cases d <;> fin_cases i <;> simp [frame,SignedSymmetry.vertex,LatticeRelay.axisCenter,
    center,outward,PlanarBoundary.outward,Equiv.swap_apply_def] <;> ring

theorem relay_cube_eq (c : Vertex) (n : ℕ) : LatticeRelay.Cube c n = cube c n := by
  ext x
  rw [mem_cube]
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ) at hh
    rw [abs_le] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ)
    rw [abs_le]
    omega

theorem image_cube (S : SignedSymmetry) (c : Vertex) (n : ℕ) : S.vertex '' cube c n = cube (S.vertex c) n := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (S.cube_map c y n).mp hy
  · intro hx
    exact ⟨S.vertex.symm x,(S.cube_map c _ n).mpr (by simpa only [Equiv.apply_symm_apply] using hx),S.vertex.apply_symm_apply x⟩

theorem prism_eq_cubes (r : ℕ) : LatticeRelay.Prism r =
    LatticeRelay.Cube 0 (10*r) ∪ LatticeRelay.Cube (LatticeRelay.axisCenter (20*(r:ℤ)+1)) (10*r) := by
  ext x
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  constructor
  · intro hx
    by_cases h : x 0 ≤ 10*(r:ℤ)
    · left
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-0| ≤ _
        rw [sub_zero,abs_le]
        exact ⟨hx.1,h⟩
      · simpa only [Pi.zero_apply,sub_zero] using hx.2.2 i hi
    · right
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-(20*(r:ℤ)+1)| ≤ _
        change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ)
        rw [abs_le]
        have hh := hx.2.1
        omega
      · simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx.2.2 i hi
  · rintro (hx|hx)
    · have hh := hx 0
      change |x 0-0| ≤ 10*(r:ℤ) at hh
      rw [sub_zero,abs_le] at hh
      refine ⟨hh.1,by omega,?_⟩
      intro i _
      simpa only [Pi.zero_apply,sub_zero] using hx i
    · have hh := hx 0
      change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ) at hh
      rw [abs_le] at hh
      refine ⟨by omega,by omega,?_⟩
      intro i hi
      simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx i

theorem frame_prism (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex '' LatticeRelay.Prism r = PairRegion r v (v+outward d) := by
  rw [prism_eq_cubes,Set.image_union]
  have he : (10:ℤ)*r = (10*r:ℕ) := by push_cast; rfl
  rw [he,relay_cube_eq,relay_cube_eq,image_cube,image_cube,frame_zero,frame_next]
  ext x
  simp only [Set.mem_union,PairRegion,Set.mem_ofPred_eq,Q,Box.contains_cube_iff]

theorem neighboring_relay {model : Model} (s : ScaleData model) (G : LatticeGraph)
    (p : model.Bit → Set.Icc (0:ℝ) 1) (v : Point) (d : Direction)
    (hG : G.ContainsSet (PairRegion s.r v (v+outward d)))
    (hp : model.UniformOn p s.q (PairRegion s.r v (v+outward d)))
    (o : G.Node) (ho : o.1 ∉ PairRegion s.r v (v+outward d)) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | (B s.r v).Contains x} ∧
      ¬G.Meets model ω o {x | (B s.r (v+outward d)).Contains x}} ≤ 13*s.η := by
  have h := s.relay_in_frame G p (frame s.r v d) (by rwa [frame_prism]) (by rwa [frame_prism]) o
    (by rwa [frame_prism])
  simpa only [frame_zero,frame_next,B,Box.contains_cube_iff,Set.ofPred_mem_eq] using h
end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

def Subgraph (G H : LatticeGraph) : Prop := G.vertices ⊆ H.vertices ∧ G.edges ⊆ H.edges

theorem conn_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {x y : G.Node} (hc : G.Conn m ω x y) :
    H.Conn m ω ⟨x.1,h.1 x.2⟩ ⟨y.1,h.1 y.2⟩ := by
  rw [G.conn_iff] at hc
  rw [H.conn_iff]
  refine ⟨?_,hc.2.lift (fun z : G.Node => (⟨z.1,h.1 z.2⟩ : H.Node)) ?_⟩
  · cases m <;> exact hc.1
  · intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,h.2 he,hi,ho⟩
    · obtain ⟨⟨e,he,hi⟩,ha,hb⟩ := hab
      exact ⟨⟨e,h.2 he,hi⟩,ha,hb⟩

theorem meets_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {o : G.Node} {T : Set Vertex} (hc : G.Meets m ω o T) :
    H.Meets m ω ⟨o.1,h.1 o.2⟩ T := by
  obtain ⟨y,hy,hc⟩ := hc
  exact ⟨⟨y.1,h.1 y.2⟩,hy,conn_inclusion h m hc⟩

noncomputable def ofBox (B : Box) : LatticeGraph where
  vertices := B.vertices
  edges := B.bonds
  left_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).1
  right_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).2

@[simp] theorem ofBox_contains (B : Box) : (ofBox B).ContainsBox B := ⟨fun _ h => h,fun _ h => h⟩
end LatticeGraph

namespace Coarse
noncomputable def linkBits : (m : Model) → ℕ → Point → Point → Finset m.Bit
  | .bond,r,v,w => interface r v w
  | .site,_,_,_ => ∅
noncomputable def block (m : Model) (r : ℕ) (v parent : Point) : Finset m.Bit :=
  (Q r v).bits m ∪ linkBits m r v parent
noncomputable def rootBits (m : Model) (r : ℕ) : Finset m.Bit :=
  (Q r 0).bits m ∪ Finset.univ.biUnion (fun d : Direction => linkBits m r 0 (outward d))
noncomputable def exposed (m : Model) (r : ℕ) (D : Finset Point) : Finset m.Bit :=
  rootBits m r ∪ D.biUnion (fun v => (Q r v).bits m) ∪
    (D ×ˢ D).biUnion (fun e => linkBits m r e.1 e.2)

theorem bits_disjoint (m : Model) (r : ℕ) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r v).bits m) ((Q r w).bits m) := by
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact h (cube_unique r ((Box.mem_bonds _ _).mp he).1 ((Box.mem_bonds _ _).mp hf).1)
  · exact Q_disjoint r h

theorem bits_link_disjoint (m : Model) (r : ℕ) (u : Point) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r u).bits m) (linkBits m r v w) := by
  cases m
  · exact internal_not_interface r h
  · exact Finset.disjoint_empty_right _

theorem block_disjoint (m : Model) (r : ℕ) {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (hw : w ∉ D) (ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block m r v a) (block m r w b) := by
  have hva : v ≠ a := fun h => hv (h ▸ ha)
  have hwb : w ≠ b := fun h => hw (h ▸ hb)
  rw [block,block,Finset.disjoint_union_left,Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  refine ⟨⟨bits_disjoint m r hvw,bits_link_disjoint m r v hwb⟩,
    ⟨(bits_link_disjoint m r w hva).symm,?_⟩⟩
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    rcases interface_eq_endpoints r he hf with h|h
    · exact hvw h.1
    · exact hv (h.1 ▸ hb)
  · exact Finset.disjoint_empty_left _

theorem block_subset_exposed_insert (m : Model) (r : ℕ) {D : Finset Point}
    {v a : Point} (ha : a ∈ D) : block m r v a ⊆ exposed m r (insert v D) := by
  intro e he
  rw [block,Finset.mem_union] at he
  rcases he with he|he
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v,Finset.mem_insert_self _ _,he⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(v,a),Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem ha⟩,he⟩)

theorem exposed_mono (m : Model) (r : ℕ) {D D' : Finset Point} (h : D ⊆ D') :
    exposed m r D ⊆ exposed m r D' := by
  intro e he
  simp only [exposed,Finset.mem_union,Finset.mem_biUnion,Finset.mem_product] at he ⊢
  rcases he with (he|⟨v,hv,he⟩)|⟨⟨v,w⟩,⟨hv,hw⟩,he⟩
  · exact Or.inl (Or.inl he)
  · exact Or.inl (Or.inr ⟨v,h hv,he⟩)
  · exact Or.inr ⟨(v,w),⟨h hv,h hw⟩,he⟩

theorem internal_pair_not_exposed (m : Model) (r : ℕ) {D : Finset Point}
    (h0 : 0 ∈ D) {v w : Point} (hv : v ∉ D) (hw : w ∉ D) {e : m.Bit}
    (he : m.Internal (PairRegion r v w) e) : e ∉ exposed m r D := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ h0)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ h0)
  cases m
  · change e ∉ _
    rw [internal_pair_bond] at he
    simp only [Finset.mem_union] at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Finset.mem_product,Finset.mem_univ,true_and]
    intro hb
    have noInternal (a : Point) (ha : a ∈ D) (h : e ∈ (Q r a).bonds) : False := by
      have hl := ((Box.mem_bonds _ _).mp h).1
      rcases he with (he|he)|he
      · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · rcases (mem_interface r v w e).mp he with he|he
        · exact hv ((cube_unique r he.1 hl) ▸ ha)
        · exact hw ((cube_unique r he.1 hl) ▸ ha)
    have noLink (a b : Point) (ha : a ∈ D) (h : e ∈ interface r a b) : False := by
      rcases (mem_interface r a b e).mp h with h|h
      · have hl := h.1
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hv ((cube_unique r he.1 hl) ▸ ha)
          · exact hw ((cube_unique r he.1 hl) ▸ ha)
      · have hl := h.2
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hw ((cube_unique r he.2 hl) ▸ ha)
          · exact hv ((cube_unique r he.2 hl) ▸ ha)
    rcases hb with ((hb|⟨d,hd⟩)|⟨a,ha,hb⟩)|⟨⟨a,b⟩,⟨ha,_⟩,hb⟩
    · exact noInternal 0 h0 hb
    · exact noLink 0 (outward d) h0 hd
    · exact noInternal a ha hb
    · exact noLink a b ha hb
  · change (Q r v).Contains e ∨ (Q r w).Contains e at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Box.mem_vertices,Finset.notMem_empty,and_false,exists_false,or_false]
    rintro (hh|⟨a,ha,hh⟩)
    · rcases he with he|he
      · exact hv0 (cube_unique r he hh)
      · exact hw0 (cube_unique r he hh)
    · rcases he with he|he
      · exact hv ((cube_unique r he hh) ▸ ha)
      · exact hw ((cube_unique r he hh) ▸ ha)

noncomputable def extendGraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : LatticeGraph where
  vertices := G.vertices ∪ (Q r x).vertices
  edges := G.edges ∪ (Q r x).bonds ∪ interface r v x
  left_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.left_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).1)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.1))
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.1)
  right_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.right_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).2)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.2)
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.2))

theorem extendGraph_subgraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : G.Subgraph (extendGraph r G v x hv) :=
  ⟨Finset.subset_union_left,fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)⟩

theorem extendGraph_contains (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsBox (Q r x) :=
  ⟨Finset.subset_union_right,fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)⟩

theorem extendGraph_bits (m : Model) (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) :
    (extendGraph r G v x hv).bits m = G.bits m ∪ block m r x v := by
  cases m
  · dsimp [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits]
    rw [interface_comm r x v,Finset.union_assoc]
  · simp only [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits,Finset.union_empty]

theorem extendGraph_pair (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsSet (PairRegion r v x) := by
  constructor
  · intro y hy
    rcases hy with hy|hy
    · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr hy))
    · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr hy)
  · intro e he hf
    have hh := (internal_pair_bond r v x e).mp ⟨he,hf⟩
    rcases Finset.mem_union.mp hh with hh|hh
    · rcases Finset.mem_union.mp hh with hh|hh
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hv.2 hh))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hh)
    · exact Finset.mem_union_right _ hh
end Coarse
end CriticalZ3

end OAI
