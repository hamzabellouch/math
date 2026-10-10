import OAI.Probability.CriticalZ3.AdaptiveReveals

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

/-- A packet stores exactly the finite parent-chain graph, extended only on assignment. -/
structure Packet (r : ℕ) where
  vertex : Point
  parent : Point
  graph : LatticeGraph
  contains : graph.ContainsBox (Q r vertex)
  root_mem : (0:Vertex) ∈ graph.vertices

namespace Packet
variable {r : ℕ}
def event (t : Packet r) (m : Model) : Set m.Config :=
  {ω | t.graph.Meets m ω ⟨0,t.root_mem⟩ {y | (B r t.vertex).Contains y}}

theorem measurableSet_event (t : Packet r) (m : Model) : MeasurableSet (t.event m) :=
  t.graph.measurableSet_meets m _ _

theorem event_determined (t : Packet r) (m : Model) :
    ProductCylinder.DeterminedBy (F := Prop) (t.graph.bits m) (fun ω => ω ∈ t.event m) :=
  t.graph.meets_determined m _ _

noncomputable def child (t : Packet r) (x : Point) : Packet r where
  vertex := x
  parent := t.vertex
  graph := extendGraph r t.graph t.vertex x t.contains
  contains := extendGraph_contains r t.graph t.vertex x t.contains
  root_mem := (extendGraph_subgraph r t.graph t.vertex x t.contains).1 t.root_mem

theorem child_bits (t : Packet r) (x : Point) (m : Model) :
    (t.child x).graph.bits m = t.graph.bits m ∪ block m r x t.vertex :=
  extendGraph_bits m r t.graph t.vertex x t.contains
end Packet

structure Exploration (m : Model) (r : ℕ) where
  history : History m.Bit
  processed : Finset Point
  queue : List (Packet r)
  good : Finset Point
  bad : Finset Point

namespace Exploration
variable {m : Model} {r : ℕ}
noncomputable def visited (s : Exploration m r) : Finset Point :=
  s.processed ∪ (s.queue.map Packet.vertex).toFinset
noncomputable def reveal (s : Exploration m r) : Finset m.Bit :=
  match s.queue with
  | [] => ∅
  | t::_ => block m r t.vertex t.parent \ s.history.known
noncomputable def after (s : Exploration m r) (ω : m.Config) : History m.Bit :=
  s.history.observe s.reveal ω
noncomputable def candidates (s : Exploration m r) (t : Packet r) : List (Packet r) :=
  (List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).filter
    (fun u => u.vertex ∉ s.visited)
noncomputable def Accept (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (t : Packet r) (ω : m.Config) : Prop :=
  (s.after ω).values ∈ t.event m ∧ ∀ u ∈ s.candidates t,
    1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
noncomputable def markedBad (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Bool :=
  match s.queue with
  | [] => false
  | t::_ => decide (¬s.Accept q δ t ω)
noncomputable def advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Exploration m r where
  history := s.after ω
  processed := match s.queue with | [] => s.processed | t::_ => insert t.vertex s.processed
  queue := match s.queue with
    | [] => []
    | t::ts => ts ++ if s.Accept q δ t ω then s.candidates t else []
  good := match s.queue with
    | [] => s.good
    | t::_ => if s.Accept q δ t ω then insert t.vertex s.good else s.good
  bad := match s.queue with
    | [] => s.bad
    | t::_ => if s.Accept q δ t ω then s.bad else insert t.vertex s.bad

theorem reveal_disjoint (s : Exploration m r) : Disjoint s.reveal s.history.known := by
  cases h : s.queue with
  | nil => simp only [reveal,h]; exact Finset.disjoint_empty_left _
  | cons t ts => simp only [reveal,h]; exact Finset.sdiff_disjoint

noncomputable def scheme (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    AdaptiveReveals.Scheme m.Bit Point (Exploration m r) where
  reveal := reveal
  parameter := fun s => s.history.parameter q
  vertex := fun s => (s.queue.head?).map Packet.vertex
  bad := fun s a => s.markedBad q δ (ProductCylinder.extend s.reveal a)
  child := fun s a => s.advance q δ (ProductCylinder.extend s.reveal a)
  parameter_child := fun s _a => s.history.parameter_observe q s.reveal _

structure Valid (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) : Prop where
  root_processed : 0 ∈ s.processed
  distinct : (s.queue.map Packet.vertex).Nodup
  unprocessed : ∀ t ∈ s.queue, t.vertex ∉ s.processed
  parents : ∀ t ∈ s.queue, t.parent ∈ s.processed
  exposed : s.history.known ⊆ Coarse.exposed m r s.processed
  support : ∀ t ∈ s.queue, t.graph.bits m ⊆ s.history.known ∪ block m r t.vertex t.parent
  promise : ∀ t ∈ s.queue, 1-δ < (ProductCylinder.law (s.history.parameter q)).real (t.event m)
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem outward_injective : Function.Injective outward := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [outward,PlanarBoundary.outward]

theorem neighbor_ne (v : Point) (d : Direction) : v+outward d ≠ v := by
  intro h
  have hh : outward d = 0 := add_left_cancel (h.trans (add_zero v).symm)
  fin_cases d <;> norm_num [outward,PlanarBoundary.outward] at hh

namespace Exploration
variable {m : Model} {r : ℕ}

@[simp] theorem mem_candidates (s : Exploration m r) (t u : Packet r) :
    u ∈ s.candidates t ↔ (∃ d : Direction, t.child (t.vertex+outward d) = u) ∧ u.vertex ∉ s.visited := by
  simp only [candidates,List.mem_filter,List.mem_ofFn,decide_eq_true_eq]

theorem queue_visited (s : Exploration m r) {t : Packet r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

theorem candidates_distinct (s : Exploration m r) (t : Packet r) :
    ((s.candidates t).map Packet.vertex).Nodup := by
  have hh : ((List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).map Packet.vertex).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro a b hab
    exact outward_injective (add_left_cancel hab)
  exact (List.filter_sublist.map Packet.vertex).nodup hh

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

theorem current_support {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    t.graph.bits m ⊆ s.history.known ∪ s.reveal := by
  intro e he
  have hh := hs.support t (by simp [hq]) he
  rcases Finset.mem_union.mp hh with hh|hh
  · exact Finset.mem_union_left _ hh
  · by_cases hk : e ∈ s.history.known
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (by simpa only [reveal,hq,Finset.mem_sdiff] using ⟨hh,hk⟩)

theorem later_disjoint {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) : Disjoint s.reveal (u.graph.bits m) := by
  have htq : t ∈ s.queue := by simp [hq]
  have huq : u ∈ s.queue := by simp [hq,hu]
  have htu : t.vertex ≠ u.vertex := by
    have hn := hs.distinct
    rw [hq,List.map_cons,List.nodup_cons] at hn
    intro he
    exact hn.1 (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩)
  have hd := block_disjoint m r (hs.unprocessed t htq) (hs.unprocessed u huq)
    (hs.parents t htq) (hs.parents u huq) htu
  apply Finset.disjoint_left.mpr
  intro e he hu
  have hr : e ∈ block m r t.vertex t.parent ∧ e ∉ s.history.known := by
    simpa only [reveal,hq,Finset.mem_sdiff] using he
  rcases Finset.mem_union.mp (hs.support u huq hu) with hu|hu
  · exact hr.2 hu
  · exact Finset.disjoint_left.mp hd hr.1 hu

theorem later_probability {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) (ω : m.Config) :
    (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m) =
      (ProductCylinder.law (s.history.parameter q)).real (u.event m) := by
  apply ProductCylinder.probability_congr_parameters (u.graph.bits m) _ _ _ _ (u.event_determined m)
  intro e he
  rw [after,History.parameter_observe]
  exact ite_eq_right (fun hh => Finset.disjoint_left.mp (later_disjoint hs hq hu) hh he)

theorem valid_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (ω : m.Config) : (s.advance q δ ω).Valid q δ := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    have htq : t ∈ s.queue := by simp [hq]
    have hnot : t.vertex ∉ ts.map Packet.vertex := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.1
    have htail : (ts.map Packet.vertex).Nodup := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.2
    have hp : (s.advance q δ ω).processed = insert t.vertex s.processed := by simp [advance,hq]
    have hn : (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
      simp [advance,hq]
    have hvu {u : Packet r} (hu : u ∈ s.candidates t) :
        u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      have hh := (mem_candidates s t u).mp hu |>.2
      exact ⟨fun he => hh (he ▸ s.queue_visited htq),fun he => hh (s.processed_visited he)⟩
    have hold {u : Packet r} (hu : u ∈ ts) : u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      exact ⟨fun he => hnot (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩),
        hs.unprocessed u (by simp [hq,hu])⟩
    have hmembers {u : Packet r} (hu : u ∈ (s.advance q δ ω).queue) :
        u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
      rw [hn,List.mem_append] at hu
      rcases hu with hu|hu
      · exact Or.inl hu
      · split_ifs at hu with ha
        · exact Or.inr ⟨ha,hu⟩
        · exact False.elim (List.not_mem_nil hu)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hp]; exact Finset.mem_insert_of_mem hs.root_processed
    · rw [hn,List.map_append]
      split_ifs with ha
      · apply htail.append (s.candidates_distinct t)
        apply List.disjoint_left.mpr
        intro v hv hu
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
        have hh := (mem_candidates s t z).mp hz |>.2
        exact hh (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hq,List.map_cons]; exact List.mem_cons_of_mem _ hv)))
      · simpa only [List.map_nil,List.append_nil] using htail
    · intro u hu
      rw [hp,Finset.mem_insert]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact not_or.mpr (hold hu)
      · exact not_or.mpr (hvu hu)
    · intro u hu
      rw [hp]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact Finset.mem_insert_of_mem (hs.parents u (by simp [hq,hu]))
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        exact Finset.mem_insert_self _ _
    · rw [hp]
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      intro e he
      rcases he with hk|hr
      · exact exposed_mono m r (Finset.subset_insert _ _) (hs.exposed hk)
      · apply block_subset_exposed_insert m r (hs.parents t htq)
        exact (Finset.mem_sdiff.mp (by simpa only [reveal,hq] using hr)).1
    · intro u hu
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      rcases hmembers hu with hu|⟨_,hu⟩
      · intro e he
        rcases Finset.mem_union.mp (hs.support u (by simp [hq,hu]) he) with he|he
        · exact Or.inl (Or.inl he)
        · exact Or.inr he
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        intro e he
        rw [Packet.child_bits,Finset.mem_union] at he
        rcases he with he|he
        · exact Or.inl (Finset.mem_union.mp (current_support hs hq he))
        · exact Or.inr he
    · intro u hu
      rcases hmembers hu with hu|⟨ha,hu⟩
      · change 1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
        rw [later_probability hs hq hu ω]
        exact hs.promise u (by simp [hq,hu])
      · exact ha.2 u hu
end Exploration
end Coarse
end CriticalZ3

end OAI
