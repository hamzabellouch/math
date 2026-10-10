import OAI.Probability.CriticalZ3.Exploration

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem after_determined (s : Exploration m r) :
    ProductCylinder.DeterminedBy s.reveal (s.after) := by
  intro ω ω' he
  unfold after History.observe
  congr 1
  funext e
  by_cases hr : e ∈ s.reveal
  · simp only [replace,ite_eq_left hr,he e hr]
  · simp only [replace,ite_eq_right hr]

theorem markedBad_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.markedBad q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [markedBad,hq,ha]

theorem advance_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.advance q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [advance,hq,h,ha]

theorem badMass_eq (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    (scheme (r := r) q δ).badMass s =
      (ProductCylinder.law (s.history.parameter q)).real {ω | s.markedBad q δ ω = true} := by
  rw [AdaptiveReveals.Scheme.badMass_eq_probability]
  congr 2
  ext ω
  change (s.markedBad q δ (ProductCylinder.extend s.reveal (s.reveal.restrict ω)) = true) ↔ _
  rw [←ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω]

noncomputable def frozenEvent (s : Exploration m r) (t : Packet r) : Set m.Config :=
  {ω | s.history.freeze ω ∈ t.event m}

theorem frozenEvent_determined {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    ProductCylinder.DeterminedBy (F := Prop) s.reveal (fun ω => ω ∈ s.frozenEvent t) :=
  s.history.freeze_determined _ (t.event_determined m) (by
    simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq)

theorem frozenEvent_probability (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (t : Packet r) :
    (ProductCylinder.law (s.history.parameter q)).real (s.frozenEvent t) =
      (ProductCylinder.law (s.history.parameter q)).real (t.event m) :=
  s.history.probability_freeze q (t.event m)

theorem accept_current_iff {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) (ω : m.Config) :
    (s.after ω).values ∈ t.event m ↔ ω ∈ s.frozenEvent t := by
  exact Eq.to_iff (s.history.observe_outcome _ (t.event_determined m)
    (by simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq) s.reveal_disjoint ω)

theorem relay_failure (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) {t : Packet sc.r} {ts : List (Packet sc.r)} (hq : s.queue = t::ts)
    (d : Direction) (hx : t.vertex+outward d ∉ s.visited) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) ≤ 13*sc.η := by
  have htq : t ∈ s.queue := by simp [hq]
  have hv := hs.unprocessed t htq
  have hxD : t.vertex+outward d ∉ s.processed := fun hh => hx (s.processed_visited hh)
  have hv0 : t.vertex ≠ 0 := fun he => hv (he ▸ hs.root_processed)
  have hx0 : t.vertex+outward d ≠ 0 := fun he => hxD (he ▸ hs.root_processed)
  have hfresh : m.UniformOn (s.history.parameter sc.q) sc.q
      (PairRegion sc.r t.vertex (t.vertex+outward d)) := by
    intro e he
    apply ite_eq_right
    intro hk
    exact internal_pair_not_exposed m sc.r hs.root_processed hv hxD he (hs.exposed hk)
  have hrelay := neighboring_relay sc (t.child (t.vertex+outward d)).graph
    (s.history.parameter sc.q) t.vertex d
    (extendGraph_pair sc.r t.graph t.vertex _ t.contains) hfresh
    ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ (zero_outside_pair sc.r hv0 hx0)
  have hi : t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ ⊆
      {ω | (t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r t.vertex).Contains y} ∧
          ¬(t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r (t.vertex+outward d)).Contains y}} := by
    intro ω hω
    exact ⟨LatticeGraph.meets_inclusion (extendGraph_subgraph sc.r t.graph t.vertex _ t.contains) m hω.1,hω.2⟩
  have heq : (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) =
      (ProductCylinder.law (s.history.parameter sc.q)).real
      (t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [s.history.ae_freeze sc.q] with ω hω
    change ((s.history.freeze ω ∈ t.event m) ∧ _) = ((ω ∈ t.event m) ∧ _)
    rw [hω]
  rw [heq]
  exact (measureReal_mono hi).trans hrelay

theorem badMass_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) :
    (scheme (r := sc.r) sc.q sc.δ).badMass s ≤ CriticalScales.contourError := by
  rw [badMass_eq]
  cases hq : s.queue with
  | nil => simpa only [markedBad,hq,Bool.false_eq_true,Set.ofPred_false,measureReal_empty] using
      CriticalScales.contourError_pos.le
  | cons t ts =>
    let μ := ProductCylinder.law (s.history.parameter sc.q)
    let H := s.frozenEvent t
    let T (d : Direction) : Set m.Config :=
      {ω | ω ∈ H ∧ t.vertex+outward d ∉ s.visited ∧
        (ProductCylinder.law ((s.after ω).parameter sc.q)).real
          ((t.child (t.vertex+outward d)).event m) ≤ 1-sc.δ}
    have hH := frozenEvent_determined hs hq
    have hHm : MeasurableSet H := ProductCylinder.measurableSet_determined _ _
      (fun ω ω' he => Eq.to_iff (hH ω ω' he))
    have hHprob : μ.real Hᶜ < sc.δ := by
      rw [measureReal_compl hHm,probReal_univ]
      have hh := hs.promise t (by simp [hq])
      have he := s.frozenEvent_probability sc.q t
      change μ.real H = μ.real (t.event m) at he
      rw [he]
      linarith
    have hT (d : Direction) : μ.real (T d) ≤ (13*sc.η)/sc.δ := by
      by_cases hx : t.vertex+outward d ∉ s.visited
      · have hh := conditional_failure_bound (s.history.parameter sc.q) s.reveal H
          ((t.child (t.vertex+outward d)).event m) hH
          ((t.child (t.vertex+outward d)).measurableSet_event m) sc.δ_range.1
          (relay_failure sc hs hq d hx)
        have he : T d = {ω | ω ∈ H ∧ conditionalProbability (s.history.parameter sc.q)
            s.reveal ((t.child (t.vertex+outward d)).event m) ω ≤ 1-sc.δ} := by
          ext ω
          simp only [T,hx,not_false_eq_true,true_and,Set.mem_ofPred_eq,after,History.parameter_observe,
            conditionalProbability]
        rwa [he]
      · have he : T d = ∅ := by ext ω; simp only [T,hx,false_and,and_false,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
        rw [he,measureReal_empty]
        exact div_nonneg (mul_nonneg (by norm_num) sc.η_range.1.le) sc.δ_range.1.le
    have hb : {ω | s.markedBad sc.q sc.δ ω = true} ⊆ Hᶜ ∪ ⋃ d, T d := by
      intro ω hω
      have hn : ¬s.Accept sc.q sc.δ t ω := by
        simpa only [Set.mem_ofPred_eq,markedBad,hq,decide_eq_true_eq] using hω
      by_cases hh : ω ∈ H
      · right
        have hcur := (accept_current_iff hs hq ω).mpr hh
        have hpred : ¬∀ u ∈ s.candidates t, 1-sc.δ <
            (ProductCylinder.law ((s.after ω).parameter sc.q)).real (u.event m) :=
          fun hp => hn ⟨hcur,hp⟩
        push Not at hpred
        obtain ⟨u,hu,hfail⟩ := hpred
        obtain ⟨⟨d,rfl⟩,hx⟩ := (mem_candidates s t u).mp hu
        exact Set.mem_iUnion.mpr ⟨d,hh,hx,hfail⟩
      · exact Or.inl hh
    calc
      _ ≤ μ.real (Hᶜ ∪ ⋃ d, T d) := measureReal_mono hb
      _ ≤ μ.real Hᶜ + μ.real (⋃ d, T d) := measureReal_union_le _ _
      _ ≤ μ.real Hᶜ + ∑ d, μ.real (T d) := add_le_add le_rfl (measureReal_iUnion_fintype_le _)
      _ ≤ μ.real Hᶜ + ∑ _d : Direction, (13*sc.η)/sc.δ :=
        add_le_add le_rfl (Finset.sum_le_sum (fun d _ => hT d))
      _ = μ.real Hᶜ + 52*sc.η/sc.δ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ sc.δ + 52*sc.η/sc.δ := add_le_add hHprob.le le_rfl
      _ ≤ CriticalScales.contourError := sc.failure_budget.le

theorem everHit_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (⋃ n, (scheme (r := sc.r) sc.q sc.δ).hit n s U) ≤ CriticalScales.contourError^U.card := by
  apply AdaptiveReveals.Scheme.everHit_bound _ (Valid sc.q sc.δ) _ CriticalScales.contourError_pos.le
    (fun _ hs => badMass_bound sc hs) _ s hs U
  intro s hs a _
  exact valid_advance hs _
end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem advance_processed (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).processed = insert t.vertex s.processed := by simp only [advance,hq]

theorem advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
  simp only [advance,hq]

theorem mem_advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t u : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    u ∈ (s.advance q δ ω).queue ↔ u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
  rw [s.advance_queue q δ ω hq,List.mem_append]
  by_cases h : s.Accept q δ t ω <;> simp [h]

theorem processed_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.processed ⊆ (s.advance q δ ω).processed := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · rw [s.advance_processed q δ ω hq]; exact Finset.subset_insert _ _

theorem good_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.good ⊆ (s.advance q δ ω).good := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem bad_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.bad ⊆ (s.advance q δ ω).bad := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

theorem visited_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.visited ⊆ (s.advance q δ ω).visited := by
  cases hq : s.queue with
  | nil => rw [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact (s.advance q δ ω).processed_visited (s.processed_advance_mono q δ ω hv)
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      rw [hq,List.mem_cons] at hu
      rcases hu with rfl|hu
      · apply (s.advance q δ ω).processed_visited
        rw [s.advance_processed q δ ω hq]
        exact Finset.mem_insert_self _ _
      · apply (s.advance q δ ω).queue_visited
        exact (s.mem_advance_queue q δ ω hq).mpr (Or.inl hu)

theorem new_visited (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {v : Point} (hv : v ∈ (s.advance q δ ω).visited) :
    v ∈ s.visited ∨ (s.Accept q δ t ω ∧ ∃ d : Direction, v = t.vertex+outward d) := by
  rcases Finset.mem_union.mp hv with hv|hv
  · rw [s.advance_processed q δ ω hq,Finset.mem_insert] at hv
    rcases hv with rfl|hv
    · exact Or.inl (s.queue_visited (by simp [hq]))
    · exact Or.inl (s.processed_visited hv)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    rcases (s.mem_advance_queue q δ ω hq).mp hu with hu|⟨ha,hu⟩
    · exact Or.inl (s.queue_visited (by simp [hq,hu]))
    · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
      exact Or.inr ⟨ha,d,rfl⟩

theorem accepted_neighbors (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    (ha : s.Accept q δ t ω) (d : Direction) :
    t.vertex+outward d ∈ (s.advance q δ ω).visited := by
  by_cases hv : t.vertex+outward d ∈ s.visited
  · exact s.visited_advance_mono q δ ω hv
  · apply (s.advance q δ ω).queue_visited (t := t.child (t.vertex+outward d))
    apply (s.mem_advance_queue q δ ω hq).mpr
    exact Or.inr ⟨ha,(mem_candidates _ _ _).mpr ⟨⟨d,rfl⟩,hv⟩⟩

structure Colored (s : Exploration m r) : Prop where
  partition : s.processed = s.good ∪ s.bad
  disjoint : Disjoint s.good s.bad

def Closed (s : Exploration m r) : Prop :=
  ∀ v ∈ s.good, ∀ d : Direction, v+outward d ∈ s.visited

def Covered (s : Exploration m r) : Prop :=
  ∀ v ∈ s.visited, v ∈ s.good ∨ ∃ u ∈ s.good, ∃ d : Direction, v = u+outward d

theorem Colored.good_processed {s : Exploration m r} (h : s.Colored) : s.good ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_left

theorem Colored.bad_processed {s : Exploration m r} (h : s.Colored) : s.bad ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_right

theorem colored_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (ω : m.Config) : (s.advance q δ ω).Colored := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    have hn := hs.unprocessed t (by simp [hq])
    have hng : t.vertex ∉ s.good := fun h => hn (hc.good_processed h)
    have hnb : t.vertex ∉ s.bad := fun h => hn (hc.bad_processed h)
    constructor
    · simp only [advance,hq]
      split_ifs <;> simp only [hc.partition,Finset.insert_union,Finset.union_insert]
    · simp only [advance,hq]
      split_ifs
      · exact Finset.disjoint_insert_left.mpr ⟨hnb,hc.disjoint⟩
      · exact Finset.disjoint_insert_right.mpr ⟨hng,hc.disjoint⟩

theorem closed_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Closed) (ω : m.Config) : (s.advance q δ ω).Closed := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv d
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact s.accepted_neighbors q δ ω hq ha d
      · exact s.visited_advance_mono q δ ω (hc _ hv d)
    · exact s.visited_advance_mono q δ ω (hc _ hv d)

theorem covered_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Covered) (ω : m.Config) : (s.advance q δ ω).Covered := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases s.new_visited q δ ω hq hv with hv|⟨ha,d,rfl⟩
    · rcases hc _ hv with hv|⟨u,hu,d,he⟩
      · exact Or.inl (s.good_advance_mono q δ ω hv)
      · exact Or.inr ⟨u,s.good_advance_mono q δ ω hu,d,he⟩
    · right
      refine ⟨t.vertex,?_,d,rfl⟩
      simp only [advance,hq,ite_eq_left ha]
      exact Finset.mem_insert_self _ _

noncomputable def run (q : Set.Icc (0:ℝ) 1) (δ : ℝ) : ℕ → Exploration m r → m.Config → Exploration m r
  | 0,s,_ => s
  | n+1,s,ω => run q δ n (s.advance q δ ω) ω

@[simp] theorem run_zero (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    run q δ 0 s ω = s := rfl

@[simp] theorem run_succ (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = run q δ n (s.advance q δ ω) ω := rfl

theorem run_succ_right (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = (run q δ n s ω).advance q δ ω := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run_succ,ih,run_succ]

theorem run_valid {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Valid q δ := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (valid_advance hs ω)

theorem run_colored {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Colored := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (valid_advance hs ω) (colored_advance hs hc ω)

theorem run_closed (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Closed) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Closed := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (closed_advance s q δ hc ω)

theorem run_covered (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Covered) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Covered := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (covered_advance s q δ hc ω)

theorem run_good_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).good) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact good_advance_mono _ _ _ _

theorem run_bad_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).bad) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact bad_advance_mono _ _ _ _

theorem run_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r} (hs : s.queue = [])
    (n : ℕ) (ω : m.Config) : run q δ n s ω = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,advance_empty s q δ ω hs,ih]

noncomputable def Good (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) : Set Point :=
  {v | ∃ n, v ∈ (run q δ n s ω).good}
noncomputable def Bad (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (v : Point) : Set m.Config :=
  {ω | ∃ n, v ∈ (run q δ n s ω).bad}

theorem initial_good_subset (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    (s.good : Set Point) ⊆ Good q δ s ω := fun _ hv => ⟨0,hv⟩

end Coarse.Exploration
end CriticalZ3

end OAI
