import OAI.Analysis.CircleDomains.Topology.PathBoundaryDetour

namespace OAI

/-! Finitely many boundary detours remove a compact set of singleton
contacts. The disks may overlap: each new boundary misses the entire
obstacle, so later detours introduce no new obstacle contacts. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem finite_boundary_detour_invariant
    {X I : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (H : Set X) (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hx : ∀ i, x ∉ closure (U i)) (hy : ∀ i, y ∉ closure (U i))
    (hb : ∀ i, IsPathConnected (frontier (U i)))
    (hmiss : ∀ i, Disjoint (frontier (U i)) H) (S : Finset I) :
    ∃ δ : Path x y,
      range δ ⊆ range γ ∪ (⋃ i ∈ S, frontier (U i)) ∧
      range δ ∩ H ⊆ (range γ ∩ H) \ (⋃ i ∈ S, U i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨γ, ?_, ?_⟩ <;> simp
  | @insert i S hi ih =>
    obtain ⟨δ, hδ, hδH⟩ := ih
    obtain ⟨ε, hε⟩ := exists_boundary_detour δ (hU i) (hx i) (hy i) (hb i)
    refine ⟨ε, ?_, ?_⟩
    · intro z hz
      rcases hε hz with hz | hz
      · rcases hδ hz.1 with hz | hz
        · exact Or.inl hz
        · right
          obtain ⟨j, hjS, hj⟩ := mem_iUnion₂.mp hz
          exact mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hjS, hj⟩
      · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hz⟩)
    · rintro z ⟨hz, hzH⟩
      rcases hε hz with hz | hz
      · obtain ⟨hzold, hzavoid⟩ := hδH ⟨hz.1, hzH⟩
        refine ⟨hzold, ?_⟩
        intro hzin
        obtain ⟨j, hjS, hj⟩ := mem_iUnion₂.mp hzin
        rcases Finset.mem_insert.mp hjS with rfl | hjS
        · exact hz.2 hj
        · exact hzavoid (mem_iUnion₂.mpr ⟨j, hjS, hj⟩)
      · exact False.elim (Set.disjoint_left.mp (hmiss i) hz hzH)

theorem exists_finite_boundary_detour
    {X I : Type*} [TopologicalSpace X] [Fintype I] {x y : X} (γ : Path x y)
    (H : Set X) (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hx : ∀ i, x ∉ closure (U i)) (hy : ∀ i, y ∉ closure (U i))
    (hb : ∀ i, IsPathConnected (frontier (U i)))
    (hmiss : ∀ i, Disjoint (frontier (U i)) H)
    (hcover : range γ ∩ H ⊆ ⋃ i, U i) :
    ∃ δ : Path x y, range δ ⊆ range γ ∪ (⋃ i, frontier (U i)) ∧
      Disjoint (range δ) H := by
  classical
  obtain ⟨δ, hδ, hδH⟩ := finite_boundary_detour_invariant γ H U hU hx hy hb hmiss Finset.univ
  refine ⟨δ, ?_, Set.disjoint_left.mpr ?_⟩
  · simpa only [Finset.mem_univ, iUnion_true] using hδ
  · intro z hz hzH
    obtain ⟨hzold, hnot⟩ := hδH ⟨hz, hzH⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hzold)
    exact hnot (mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem exists_path_avoiding_from_local_boundary_detours
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (γ : Path x y)
    {H V : Set X} (hH : IsClosed H) (hγV : range γ ⊆ V)
    (hlocal : ∀ z ∈ range γ ∩ H, ∃ U : Set X,
      IsOpen U ∧ z ∈ U ∧ closure U ⊆ V ∧ x ∉ closure U ∧ y ∉ closure U ∧
        IsPathConnected (frontier U) ∧ Disjoint (frontier U) H) :
    ∃ δ : Path x y, range δ ⊆ V ∧ Disjoint (range δ) H := by
  classical
  let K := range γ ∩ H
  have hK : IsCompact K := (isCompact_range γ.continuous).inter_right hH
  choose U hU hzU hUV hxU hyU hb hm using fun z : K => hlocal z.val z.property
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hU hcover
  let W : S → Set X := fun i => U i.val
  have hcov : range γ ∩ H ⊆ ⋃ i : S, W i := by
    intro z hz
    obtain ⟨i, hiS, hzi⟩ := mem_iUnion₂.mp (hS hz)
    exact mem_iUnion.mpr ⟨⟨i, hiS⟩, hzi⟩
  obtain ⟨δ, hδ, hd⟩ := exists_finite_boundary_detour γ H W
    (fun i => hU i.val) (fun i => hxU i.val) (fun i => hyU i.val)
    (fun i => hb i.val) (fun i => hm i.val) hcov
  refine ⟨δ, ?_, hd⟩
  intro z hz
  rcases hδ hz with hz | hz
  · exact hγV hz
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hUV i.val (frontier_subset_closure hi)

end CircleDomainRigidity

end

end OAI
