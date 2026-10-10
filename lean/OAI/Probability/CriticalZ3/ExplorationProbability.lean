import OAI.Probability.CriticalZ3.ExplorationInvariant

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem run_add (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (a b : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (a+b) s ω = run q δ b (run q δ a s ω) ω := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,run_zero]
  | succ a ih => rw [Nat.succ_add,run_succ,ih,run_succ]

theorem run_stable (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N k : ℕ} (hN : (run q δ N s ω).queue = []) (hk : N ≤ k) :
    run q δ k s ω = run q δ N s ω := by
  rw [←Nat.add_sub_of_le hk,run_add]
  exact run_empty q δ hN _ ω

theorem good_eq_of_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N : ℕ} (hN : (run q δ N s ω).queue = []) :
    Good q δ s ω = ((run q δ N s ω).good : Set Point) := by
  ext v
  constructor
  · rintro ⟨k,hk⟩
    have hh := run_good_mono q δ s ω (show k ≤ N+k by omega) hk
    dsimp only at hh
    rwa [run_stable q δ s ω hN (show N ≤ N+k by omega)] at hh
  · intro h; exact ⟨N,h⟩

theorem exists_empty_of_finite_good {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Covered) (ω : m.Config) (hfin : (Good q δ s ω).Finite) :
    ∃ n, (run q δ n s ω).queue = [] := by
  let X := Good q δ s ω
  let F := X ∪ ⋃ d : Direction, (fun v : Point => v+outward d) '' X
  have hF : F.Finite := hfin.union (Set.finite_iUnion (fun d => hfin.image _))
  have hbound (n : ℕ) : (run q δ n s ω).processed ⊆ hF.toFinset := by
    intro v hv
    apply hF.mem_toFinset.mpr
    have hh := run_covered q δ hc n ω v ((run q δ n s ω).processed_visited hv)
    rcases hh with hv|⟨u,hu,d,rfl⟩
    · exact Or.inl ⟨n,hv⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨d,u,⟨n,hu⟩,rfl⟩)
  by_contra! hn
  have hcard (n : ℕ) : s.processed.card+n ≤ (run q δ n s ω).processed.card := by
    induction n with
    | zero => simp only [run_zero,Nat.add_zero,le_refl]
    | succ n ih =>
      have hvalid := run_valid hs n ω
      cases hq : (run q δ n s ω).queue with
      | nil => exact False.elim (hn n hq)
      | cons t ts =>
        rw [run_succ_right,advance_processed _ q δ ω hq,
          Finset.card_insert_of_notMem (hvalid.unprocessed t (by simp [hq]))]
        omega
  have hh := (hcard (hF.toFinset.card+1)).trans (Finset.card_le_card (hbound _))
  omega

theorem outside_bad {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hclosed : s.Closed) (hcovered : s.Covered)
    (ω : m.Config) (hfin : (Good q δ s ω).Finite)
    {x : Point} (hx : x ∈ Good q δ s ω) (d : Direction)
    (hy : x+outward d ∉ Good q δ s ω) : ω ∈ Bad q δ s (x+outward d) := by
  obtain ⟨N,hN⟩ := exists_empty_of_finite_good hs hcovered ω hfin
  have he := good_eq_of_empty q δ s ω hN
  have hxN : x ∈ (run q δ N s ω).good := by
    change x ∈ ((run q δ N s ω).good : Set Point)
    rwa [←he]
  have hv := run_closed q δ hclosed N ω x hxN d
  have hp : x+outward d ∈ (run q δ N s ω).processed := by
    simpa only [visited,hN,List.map_nil,List.toFinset_nil,Finset.union_empty] using hv
  rw [(run_colored hs hc N ω).partition,Finset.mem_union] at hp
  rcases hp with hg|hb
  · exact False.elim (hy ⟨N,hg⟩)
  · exact ⟨N,hb⟩

theorem hit_of_bad_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) (U : Finset Point)
    (hd : Disjoint U s.processed) (hU : U ⊆ (run q δ n s ω).bad) :
    ω ∈ (scheme (r := r) q δ).hit n s U := by
  induction n generalizing s U with
  | zero =>
    have he : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
    rw [he,AdaptiveReveals.Scheme.hit_empty]
    trivial
  | succ n ih =>
    cases hq : s.queue with
    | nil =>
      have he : U = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        rw [run_empty q δ hq] at hU
        exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
      rw [he,AdaptiveReveals.Scheme.hit_empty]
      trivial
    | cons t ts =>
      have hchild : (scheme (r := r) q δ).child s (s.reveal.restrict ω) = s.advance q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.advance_determined q δ) ω).symm
      have hbad : (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = s.markedBad q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω).symm
      have hv : (scheme (r := r) q δ).vertex s = some t.vertex := by simp only [scheme,hq,List.head?_cons,Option.map_some]
      rw [AdaptiveReveals.Scheme.hit,hv]
      change (t.vertex ∈ U → (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = true) ∧
        ω ∈ (scheme (r := r) q δ).hit n
          ((scheme (r := r) q δ).child s (s.reveal.restrict ω)) (U.erase t.vertex)
      rw [hchild,hbad]
      constructor
      · intro hv
        have hna : ¬s.Accept q δ t ω := by
          intro ha
          have hg : t.vertex ∈ (s.advance q δ ω).good := by
            simp only [advance,hq,ite_eq_left ha]; exact Finset.mem_insert_self _ _
          have hg' := run_good_mono q δ (s.advance q δ ω) ω (Nat.zero_le n) hg
          exact Finset.disjoint_left.mp (run_colored hs hc (n+1) ω).disjoint hg' (hU hv)
        simpa only [markedBad,hq,decide_eq_true_eq] using hna
      · apply ih (valid_advance hs ω) (colored_advance hs hc ω) (U.erase t.vertex)
        · apply Finset.disjoint_left.mpr
          intro v hv hp
          rw [advance_processed s q δ ω hq,Finset.mem_insert] at hp
          rcases hp with he|hp
          · exact (Finset.mem_erase.mp hv).1 he
          · exact Finset.disjoint_left.mp hd (Finset.mem_of_mem_erase hv) hp
        · exact Finset.Subset.trans (Finset.erase_subset _ _) hU

theorem exists_bad_time (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r)
    (ω : m.Config) (U : Finset Point) (hU : ∀ v ∈ U, ω ∈ Bad q δ s v) :
    ∃ n, U ⊆ (run q δ n s ω).bad := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0,Finset.empty_subset _⟩
  | @insert a U ha ih =>
    obtain ⟨k,hk⟩ := hU a (Finset.mem_insert_self _ _)
    obtain ⟨n,hn⟩ := ih (fun v hv => hU v (Finset.mem_insert_of_mem hv))
    refine ⟨max k n,?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact run_bad_mono q δ s ω (le_max_left _ _) hk
    · exact run_bad_mono q δ s ω (le_max_right _ _) (hn hv)

theorem bad_set_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    {ω | ∀ v ∈ U, ω ∈ Bad q δ s v} ⊆ ⋃ n, (scheme (r := r) q δ).hit n s U := by
  intro ω hω
  obtain ⟨n,hn⟩ := exists_bad_time q δ s ω U hω
  apply Set.mem_iUnion.mpr
  refine ⟨n,hit_of_bad_subset hs hc n ω U ?_ hn⟩
  apply Finset.disjoint_left.mpr
  intro v hv hp
  have hg : v ∈ s.good := by simpa only [hc.partition,hb,Finset.union_empty] using hp
  have hgn := run_good_mono q δ s ω (Nat.zero_le n) hg
  exact Finset.disjoint_left.mp (run_colored hs hc n ω).disjoint hgn (hn hv)

theorem bad_set_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | ∀ v ∈ U, ω ∈ Bad sc.q sc.δ s v} ≤ CriticalScales.contourError^U.card :=
  (measureReal_mono (bad_set_subset hs hc hb U)).trans (everHit_bound sc hs U)

theorem finite_good_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅)
    (hclosed : s.Closed) (hcovered : s.Covered) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | (Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Good sc.q sc.δ s ω} ≤ 25/144 := by
  apply PlanarBoundary.finite_good_bound _ (Good sc.q sc.δ s) (Bad sc.q sc.δ s)
    (fun ω hfin x hx d hy => outside_bad hs hc hclosed hcovered ω hfin hx d hy)
    (fun U => bad_set_bound sc hs hc hb U)

end Coarse.Exploration
end CriticalZ3

end OAI
