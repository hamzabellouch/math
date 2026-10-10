import OAI.Dynamics.EntropyCounterexample.EntropyCoding
import OAI.Dynamics.EntropyCounterexample.SparseVisits

namespace OAI

namespace Problem340.EntropyCoding

open Set SetRel Dynamics

theorem exceptionalBlocks_card_eq_outsideVisitsCount {X : Type*}
    (T : X → X) (V : Set X) (m r : ℕ) (x : X) :
    (exceptionalBlocks T V m r x).card = outsideVisitsCount (T^[m]) V r x := by
  classical
  unfold exceptionalBlocks outsideVisitsCount
  simp only [← Function.iterate_mul]
  exact card_filter_fin_eq_range r (fun i => T^[m * i] x ∉ V)

theorem coverMincard_le_of_sparse_visits_finset {X : Type*} [Nonempty X]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p q : Finset X) (hpne : p.Nonempty) (hqne : q.Nonempty)
    (hp : IsDynCoverOf T V U m p) (hq : IsDynCoverOf T Set.univ U m q)
    (hsparse : ∀ x, outsideVisitsCount (T^[m]) V r x ≤ k) :
    coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * p.card ^ r * q.card ^ k : ℕ) := by
  classical
  let : Nonempty p := Finset.Nonempty.coe_sort hpne
  let : Nonempty q := Finset.Nonempty.coe_sort hqne
  have hp' : ∀ x ∈ V, ∃ a : p, (x, (a : X)) ∈ dynEntourage T U m := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hp hx
    exact ⟨⟨a, ha⟩, hax⟩
  have hq' : ∀ x, ∃ b : q, (x, (b : X)) ∈ dynEntourage T U m := by
    intro x
    obtain ⟨b, hb, hbx⟩ := hq (Set.mem_univ x)
    exact ⟨⟨b, hb⟩, hbx⟩
  have hsparse' : ∀ x, (exceptionalBlocks T V m r x).card ≤ k := by
    intro x
    rw [exceptionalBlocks_card_eq_outsideVisitsCount]
    exact hsparse x
  simpa only [Fintype.card_coe] using
    coverMincard_le_of_sparse_visits T U m r k V
      (fun a : p => (a : X)) (fun b : q => (b : X)) hp' hq' hsparse'

theorem exists_open_neighborhood_dynCover {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) {U : SetRel X X} (hU : IsOpen U)
    {K : Set X} {m : ℕ} {p : Finset X} (hp : IsDynCoverOf T K U m p) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ IsDynCoverOf T V U m p := by
  let V : Set X := ⋃ a ∈ p, {x | (x, a) ∈ dynEntourage T U m}
  have hopen : IsOpen V := by
    apply isOpen_iUnion
    intro a
    apply isOpen_iUnion
    intro _
    exact (isOpen.dynEntourage hT hU m).preimage (continuous_id.prodMk continuous_const)
  refine ⟨V, hopen, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hp hx
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hxa⟩⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨a, ha, hxa⟩

theorem exists_sparse_cover_bound_of_attraction {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [Nonempty X]
    {T : X → X} (hT : Continuous T) {K V : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V)
    (hattract : ∀ x, Filter.Tendsto
      (fun n => Metric.infDist (T^[n] x) K) Filter.atTop (nhds 0))
    (U : SetRel X X) [U.IsSymm] {m : ℕ} (hm : 0 < m)
    (p q : Finset X) (hpne : p.Nonempty) (hqne : q.Nonempty)
    (hp : IsDynCoverOf T V U m p) (hq : IsDynCoverOf T Set.univ U m q)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ r : ℕ,
      coverMincard T Set.univ (U ○ U) (m * r) ≤
        (2 ^ r * p.card ^ r * q.card ^ ⌈τ * r + J⌉₊ : ℕ) := by
  obtain ⟨J, hJ⟩ := exists_sparse_blocks_of_attraction hT hK hne hV hKV hattract hm hτ
  refine ⟨J, fun r => ?_⟩
  apply coverMincard_le_of_sparse_visits_finset T U m r ⌈τ * r + J⌉₊ V p q hpne hqne hp hq
  intro x
  have h := (hJ r x).trans (Nat.le_ceil (τ * r + J))
  exact_mod_cast h

end Problem340.EntropyCoding

end OAI
