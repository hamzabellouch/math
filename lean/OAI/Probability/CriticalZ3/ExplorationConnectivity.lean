import OAI.Probability.CriticalZ3.ExplorationProbability

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace LatticeGraph

theorem Subgraph.containsBox {G H : LatticeGraph} (h : G.Subgraph H) {B : Box}
    (hB : G.ContainsBox B) : H.ContainsBox B :=
  ⟨hB.1.trans h.1,hB.2.trans h.2⟩

theorem seedReaches_witness (G : LatticeGraph) (m : Model) {c : Vertex} {a b : ℕ}
    (hab : a ≤ b) (hB : G.ContainsBox (Box.cube c b)) {T : Set Vertex} {ω : m.Config}
    (hE : ω ∈ m.SeedReaches c a b T) :
    ∃ x y : G.Node, x.1 ∈ cube c a ∧ y.1 ∈ T ∧ G.Conn m ω x y := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  refine ⟨x',y',hxa,hy,(G.conn_iff m ω x' y').mpr ⟨?_,?_⟩⟩
  · cases m <;> exact hxo
  · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
    · intro x y h
      exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
    · intro x y h
      exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
        (Box.contains_cube_iff.mpr h.2.1) h.2.2
end LatticeGraph

namespace Coarse

def facingFace (d : Direction) : FaceIndex :=
  (if d = 0 ∨ d = 2 then 1 else 0,fun _ => decide (d = 0 ∨ d = 3))

theorem facing_neighbor (r : ℕ) (d : Direction) {y : Vertex}
    (hy : y ∈ QuarterFace (center r (outward d)) (10*r) (facingFace d)) :
    ∃ z : Vertex, (Q r 0).Contains z ∧ NearestNeighbor z y := by
  have hQ := (quarterFace_subset_boundary _ _ _ hy).1
  rw [mem_cube] at hQ
  have h0 := hQ 0
  have h1 := hQ 1
  have h2 := hQ 2
  have hface := hy.1
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  fin_cases d <;>
    simp [facingFace,center,outward,PlanarBoundary.outward] at hface h0 h1 h2
  · refine ⟨step y 1,?_,1,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega
  · let z := Function.update y 0 (y 0-1)
    refine ⟨z,?_,0,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 0
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · let z := Function.update y 1 (y 1-1)
    refine ⟨z,?_,1,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 1
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · refine ⟨step y 0,?_,0,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega

noncomputable def rootPacket (r : ℕ) : Packet r where
  vertex := 0
  parent := 0
  graph := LatticeGraph.ofBox (Q r 0)
  contains := LatticeGraph.ofBox_contains _
  root_mem := (Box.mem_vertices _ _).mpr (zero_in_Q r)

noncomputable def initial (m : Model) (r : ℕ) : Exploration m r where
  history := ⟨rootBits m r,fun _ => true⟩
  processed := {0}
  queue := List.ofFn (fun d : Direction => (rootPacket r).child (outward d))
  good := {0}
  bad := ∅

theorem root_internal_disjoint (m : Model) (r : ℕ) (d : Direction) :
    Disjoint (rootBits m r) ((Q r (outward d)).bits m) := by
  rw [rootBits,Finset.disjoint_union_left]
  constructor
  · exact bits_disjoint m r (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 d))
  · apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp
      (bits_link_disjoint m r (outward d) (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 j))) hi he

theorem initial_seed_event (m : Model) (r a : ℕ) (ha : a ≤ 4*r) (d : Direction)
    {ω : m.Config} (hO : ω ∈ allValue (rootBits m r) true)
    (hE : ω ∈ m.SeedReaches (center r (outward d)) a (10*r)
      (QuarterFace (center r (outward d)) (10*r) (facingFace d))) :
    ω ∈ ((rootPacket r).child (outward d)).event m := by
  let t := (rootPacket r).child (outward d)
  let G := t.graph
  have hB : G.ContainsBox (Q r (outward d)) := t.contains
  have hroot : G.ContainsBox (Q r 0) :=
    (extendGraph_subgraph r (rootPacket r).graph 0 (outward d) (rootPacket r).contains).containsBox
      (rootPacket r).contains
  obtain ⟨x,y,hxa,hy,hxy⟩ := G.seedReaches_witness m (by omega) hB hE
  obtain ⟨z,hz,hzy⟩ := facing_neighbor r d hy
  let z' : G.Node := ⟨z,G.containsBox_node hroot hz⟩
  let o : G.Node := ⟨0,t.root_mem⟩
  have hrootOpen : ∀ e ∈ (Q r 0).bits m, ω e = true :=
    fun e he => hO e (Finset.mem_union_left _ he)
  have hoz : G.Conn m ω o z' := G.open_box_conn m hroot hrootOpen (zero_in_Q r) hz
  have hzy' : G.Adj m ω z' y := by
    obtain ⟨e,he⟩ := LatticeGraph.neighbor_incidence hzy
    have hi : e ∈ interface r 0 (outward d) := by
      rw [mem_interface]
      have hyQ : (Q r (outward d)).Contains y.1 :=
        Box.contains_cube_iff.mpr (quarterFace_subset_boundary _ _ _ hy).1
      rcases he with ⟨he0,he1⟩ | ⟨he0,he1⟩
      · exact Or.inl ⟨he0 ▸ hz,he1 ▸ hyQ⟩
      · exact Or.inr ⟨he0 ▸ hyQ,he1 ▸ hz⟩
    have hedge : e ∈ G.edges := Finset.mem_union_right _ hi
    cases m
    · exact ⟨e,hedge,he,hO e (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,hi⟩))⟩
    · exact ⟨⟨e,hedge,he⟩,(G.conn_open .site hoz).2,(G.conn_open .site hxy).2⟩
  refine ⟨x,Box.contains_cube_iff.mpr (cube_mono _ ha hxa),?_⟩
  exact G.conn_trans m hoz (G.conn_trans m (G.conn_adj m hzy') (G.conn_symm m hxy))

theorem initial_promise {m : Model} (sc : ScaleData m) (d : Direction) :
    1-sc.δ < (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
      (((rootPacket sc.r).child (outward d)).event m) := by
  let E := m.SeedReaches (center sc.r (outward d)) sc.seed (10*sc.r)
    (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have ha : sc.seed ≤ 4*sc.r := by have := sc.seed_R; have := sc.large_r; omega
  have hdet := m.seedReaches_determined (center sc.r (outward d)) sc.seed (10*sc.r)
    (by omega) (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have heq : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E =
      (ProductCylinder.law (fun _ : m.Bit => sc.q)).real E :=
    fixed_determined_probability _ _ _ (root_internal_disjoint m sc.r d) _ _ hdet
  have hle : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E ≤
      (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
        (((rootPacket sc.r).child (outward d)).event m) := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    exact fun hE => initial_seed_event m sc.r sc.seed ha d hω hE
  have hh := sc.faces (10*sc.r) (by simp) (center sc.r (outward d)) (facingFace d)
  rw [heq] at hle
  exact (sub_lt_sub_left sc.γδ 1).trans (hh.trans_le hle)

@[simp] theorem mem_initial_queue (m : Model) (r : ℕ) (t : Packet r) :
    t ∈ (initial m r).queue ↔ ∃ d : Direction, (rootPacket r).child (outward d) = t := by
  simp only [initial,List.mem_ofFn]

theorem initial_valid {m : Model} (sc : ScaleData m) : (initial m sc.r).Valid sc.q sc.δ := by
  constructor
  · exact Finset.mem_singleton_self _
  · change ((List.ofFn (fun d : Direction => (rootPacket sc.r).child (outward d))).map Packet.vertex).Nodup
    rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr outward_injective
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    simpa only [initial,Packet.child,Finset.mem_singleton,zero_add] using neighbor_ne 0 d
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Finset.mem_singleton_self _
  · intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    rw [Packet.child_bits]
    apply Finset.union_subset_union ?_ (Finset.Subset.refl _)
    change (LatticeGraph.ofBox (Q sc.r 0)).bits m ⊆ rootBits m sc.r
    have he : (LatticeGraph.ofBox (Q sc.r 0)).bits m = (Q sc.r 0).bits m := by cases m <;> rfl
    rw [he]
    exact Finset.subset_union_left
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact initial_promise sc d

theorem initial_colored (m : Model) (r : ℕ) : (initial m r).Colored := by
  constructor
  · simp only [initial,Finset.union_empty]
  · exact Finset.disjoint_empty_right _

theorem initial_closed (m : Model) (r : ℕ) : (initial m r).Closed := by
  intro v hv d
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  rw [zero_add]
  apply Exploration.queue_visited (initial m r) (t := (rootPacket r).child (outward d))
  exact (mem_initial_queue _ _ _).mpr ⟨d,rfl⟩

theorem initial_covered (m : Model) (r : ℕ) : (initial m r).Covered := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Or.inl hv
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Or.inr ⟨0,Finset.mem_singleton_self _,d,(zero_add _).symm⟩

end Coarse
end CriticalZ3

end OAI
