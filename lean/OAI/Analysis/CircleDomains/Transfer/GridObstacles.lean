import OAI.Analysis.CircleDomains.Topology.ComponentLocalization

namespace OAI

/-!
# Singleton components of the lower-grid obstacle

At a free point, each coordinate has a unique trace, so at most one of its
finitely many distinct grid levels contains the point. Pointwise
compatibility for these choices excludes a nondegenerate component of
the lower-grid union. Boundary bumping removes all the other levels,
and adjoining compact totally disconnected dust preserves the singleton.
This is the topological reduction in Step 3 of finite transfer.
-/

open Set Function

namespace CircleDomainRigidity

/-- Pointwise compatibility for every selection of one level per active
label controls the entire finite grid near a point with unique traces. -/
theorem component_finite_grid_eq_singleton
    {X I J : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype I] [Fintype J] [Nonempty J]
    (H : I → J → Set X) (hH : ∀ i j, IsClosed (H i j)) {x : X}
    (hx : x ∈ ⋃ i, ⋃ j, H i j)
    (hunique : ∀ i j k, x ∈ H i j → x ∈ H i k → j = k)
    (hcompat : ∀ (A : Finset I) (k : I → J),
      ¬ (connectedComponentIn (⋃ i ∈ A, H i (k i)) x).Nontrivial) :
    connectedComponentIn (⋃ i, ⋃ j, H i j) x = {x} := by
  classical
  let A : Finset I := Finset.univ.filter (fun i => ∃ j, x ∈ H i j)
  let k : I → J := fun i =>
    if hi : ∃ j, x ∈ H i j then Classical.choose hi else Classical.choice inferInstance
  have hk (i : I) (hi : i ∈ A) : x ∈ H i (k i) := by
    have hi' : ∃ j, x ∈ H i j := (Finset.mem_filter.mp hi).2
    simpa only [k, dite_eq_left hi'] using Classical.choose_spec hi'
  have hpresent : (⋃ p ∈ (Finset.univ : Finset (I × J)),
      ⋃ (_ : x ∈ H p.1 p.2), H p.1 p.2) = ⋃ i ∈ A, H i (k i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨⟨i, j⟩, _, hxij, hyij⟩ := by
        simpa only [mem_iUnion, exists_prop] using hy
      have hi : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hxij⟩⟩
      have heq : j = k i := hunique i j (k i) hxij (hk i hi)
      exact mem_iUnion₂.mpr ⟨i, hi, heq ▸ hyij⟩
    · intro hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨(i, k i), Finset.mem_univ _, mem_iUnion.mpr ⟨hk i hi, hyi⟩⟩
  have hxA : x ∈ ⋃ i ∈ A, H i (k i) := by
    obtain ⟨i, j, hxij⟩ := by simpa only [mem_iUnion] using hx
    have hi : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hxij⟩⟩
    exact mem_iUnion₂.mpr ⟨i, hi, hk i hi⟩
  have hsingle : connectedComponentIn (⋃ i ∈ A, H i (k i)) x = {x} :=
    (Set.not_nontrivial_iff.mp (hcompat A k)).eq_singleton_of_mem
      (mem_connectedComponentIn hxA)
  have hfull : (⋃ p ∈ (Finset.univ : Finset (I × J)), H p.1 p.2) =
      ⋃ i, ⋃ j, H i j := by
    ext y
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and, Prod.exists]
  rw [← hfull]
  apply component_finite_union_eq_singleton Finset.univ (fun p : I × J => H p.1 p.2)
    (fun p _ => hH p.1 p.2)
  · rwa [hfull]
  · rwa [hpresent]

/-- Adjoining dust creates no nondegenerate component through such a
point. The assertion also covers points absent from every lower grid. -/
theorem component_lower_grid_union_dust_eq_singleton
    {X I J : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype I] [Fintype J] [Nonempty J]
    (H : I → J → Set X) (hH : ∀ i j, IsClosed (H i j))
    {B : Set X} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    {x : X} (hxB : x ∈ B)
    (hunique : ∀ i j k, x ∈ H i j → x ∈ H i k → j = k)
    (hcompat : ∀ (A : Finset I) (k : I → J),
      ¬ (connectedComponentIn (⋃ i ∈ A, H i (k i)) x).Nontrivial) :
    connectedComponentIn ((⋃ i, ⋃ j, H i j) ∪ B) x = {x} := by
  apply component_union_dust_eq_singleton
    (isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite (hH i)))
    hB hTD (Or.inr hxB)
  intro hx
  exact component_finite_grid_eq_singleton H hH hx hunique hcompat

end CircleDomainRigidity

end OAI
