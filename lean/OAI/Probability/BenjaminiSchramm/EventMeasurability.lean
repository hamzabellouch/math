import OAI.Probability.BenjaminiSchramm.PublishedConsequences

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem volumeEvent_eq_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    volumeEvent G x n = clusterLarge G x n := by
  ext ω
  constructor
  · intro h
    by_cases hf : (cluster G ω x).Finite
    · have hn : n ≤ (cluster G ω x).ncard := by
        change (n : ℕ∞) ≤ (cluster G ω x).encard at h
        rw [← hf.cast_ncard_eq] at h
        exact_mod_cast h
      exact ⟨hf.toFinset, by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hn,
        fun y hy => hf.mem_toFinset.mp hy⟩
    · obtain ⟨t, ht, hn⟩ := (Set.not_finite.mp hf).exists_subset_card_eq n
      exact ⟨t, hn.ge, ht⟩
  · rintro ⟨t, hn, ht⟩
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hsub : (t : Set V) ⊆ cluster G ω x := ht
    have hcard := Set.encard_le_encard hsub
    have hn' : (n : ℕ∞) ≤ (t.card : ℕ∞) := by exact_mod_cast hn
    exact hn'.trans (by simpa using hcard)

theorem measurableSet_volumeEvent [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge]
  exact measurableSet_clusterLarge G x n

theorem measurableSet_extrinsicRadiusEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (extrinsicRadiusEvent G x n) := by
  exact (Measurable.exists fun y =>
    (measurableSet_setOfPred.mp (measurableSet_conn G x y)).and measurable_const).setOf

theorem along_exists_walk_length_le (G : BondGraph V E) (ω : Set E)
    {x y : V} {l : List E} (h : Along G x l y) (ho : ∀ e ∈ l, e ∈ ω) :
    ∃ w : (openSimpleGraph G ω).Walk x y, w.length ≤ l.length := by
  induction h with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x z y l e he h ih =>
    obtain ⟨w, hw⟩ := ih (fun f hf => ho f (by simp [hf]))
    by_cases hxz : x = z
    · subst z
      exact ⟨w, hw.trans (by simp)⟩
    · refine ⟨.cons ⟨hxz, e, ho e (by simp), he⟩ w, ?_⟩
      change w.length + 1 ≤ l.length + 1
      exact Nat.add_le_add_right hw 1

theorem intrinsicBall_iff_distance_le (G : BondGraph V E) (ω : Set E)
    (x y : V) (M : ℕ) (hc : Conn G ω x y) :
    y ∈ intrinsicBall G ω x M ↔ (openSimpleGraph G ω).dist x y ≤ M := by
  constructor
  · rintro ⟨l, hl, hlen, ho⟩
    obtain ⟨w, hw⟩ := along_exists_walk_length_le G ω hl ho
    exact (SimpleGraph.dist_le w).trans (hw.trans hlen)
  · intro hd
    obtain ⟨w, hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
    obtain ⟨l, hl, he, ho⟩ := walk_lift_bonds G ω w
    have hlen : l.length = w.length := by
      have he' := congrArg List.length he
      simpa only [List.length_map, SimpleGraph.Walk.length_edges] using he'
    exact ⟨l, hl, hlen.trans_le (hw.trans_le hd), ho⟩

theorem measurableSet_mem_intrinsicBall (G : BondGraph V E) (hloc : LocallyFinite G)
    (x y : V) (M : ℕ) : MeasurableSet {ω | y ∈ intrinsicBall G ω x M} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω | y ∈ intrinsicBall G ω x M} =
      {ω | ω ∩ (Q : Set E) ∈ {η | y ∈ intrinsicBall G η x M}} := by
    ext ω
    change (y ∈ intrinsicBall G ω x M) ↔ (y ∈ intrinsicBall G (ω ∩ (Q : Set E)) x M)
    rw [intrinsicBall_restrict G hloc]
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem intrinsicRadiusEvent_eq (G : BondGraph V E) (x : V) {n : ℕ} (hn : 0 < n) :
    intrinsicRadiusEvent G x n =
      {ω | ∃ y, Conn G ω x y ∧ y ∉ intrinsicBall G ω x (n - 1)} := by
  ext ω
  constructor
  · rintro ⟨y, hy, hd⟩
    refine ⟨y, hy, ?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n - 1) hy]
    omega
  · rintro ⟨y, hy, hd⟩
    refine ⟨y, hy, ?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n - 1) hy] at hd
    omega

theorem measurableSet_intrinsicRadiusEvent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (n : ℕ) :
    MeasurableSet (intrinsicRadiusEvent G x n) := by
  by_cases hn : n = 0
  · subst n
    have he : intrinsicRadiusEvent G x 0 = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact ⟨x, mem_cluster_self G ω x, Nat.zero_le _⟩
    rw [he]
    exact MeasurableSet.univ
  · rw [intrinsicRadiusEvent_eq G x (Nat.pos_of_ne_zero hn)]
    exact (Measurable.exists fun y =>
      (measurableSet_setOfPred.mp (measurableSet_conn G x y)).and
      (measurableSet_setOfPred.mp
        (measurableSet_mem_intrinsicBall G hloc x y (n - 1))).not).setOf

end Percolation.BenjaminiSchramm

end OAI
