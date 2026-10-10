import OAI.Analysis.CircleDomains.Topology.ClopenNeighborhood

namespace OAI

/-!
# Localizing nondegenerate components

Boundary bumping turns a nondegenerate continuum through a point into
one in any prescribed neighborhood. This is the localization used in
the lower-grid obstacle argument. Totally disconnected dust cannot
destroy a singleton component of a compact closed obstacle.
-/

open Set Topology

namespace CircleDomainRigidity

theorem exists_nontrivial_subcontinuum_in_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C U : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) {x : X} (hx : x ∈ C) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D.Nontrivial ∧ x ∈ D ∧ D ⊆ C ∩ U := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := (Subtype.val ⁻¹' U) ∩ {yc}ᶜ
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxU, fun heq => hyx (congrArg Subtype.val heq).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro heq
    have hyN : yc ∈ N := by rw [heq]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  let K := connectedComponentIn N xc
  have hKclosed : IsClosed K := by
    change IsClosed (connectedComponentIn N xc)
    rw [connectedComponentIn_eq_image hxN]
    exact hNclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hxN
  let D : Set X := Subtype.val '' K
  have hxD : x ∈ D := ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hzx : z.val ≠ x := by
    intro heq
    have hzc : z = xc := Subtype.ext heq
    have hxfront : xc ∈ frontier N := hzc ▸ hzfront
    exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)
  refine ⟨D, hKclosed.isCompact.image continuous_subtype_val,
    hKconn.image _ continuous_subtype_val.continuousOn,
    ⟨x, hxD, z.val, hzD, hzx.symm⟩, hxD, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.property, (hNO (connectedComponentIn_subset N xc hw)).1⟩

/-- To rule out a nondegenerate component, it suffices to rule out small
subcontinua through the point in one open neighborhood. -/
theorem component_eq_singleton_of_local_no_continuum
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F U : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hno : ∀ D : Set X, IsCompact D → IsConnected D → x ∈ D →
      D ⊆ F ∩ U → ¬ D.Nontrivial) :
    connectedComponentIn F x = {x} := by
  have hclosed : IsClosed (connectedComponentIn F x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn := isConnected_connectedComponentIn_iff.mpr hx
  have hsub : (connectedComponentIn F x).Subsingleton := by
    by_contra hn
    have hnt : (connectedComponentIn F x).Nontrivial := Set.not_subsingleton_iff.mp hn
    obtain ⟨D, hDcompact, hDconn, hDnt, hxD, hDsub⟩ :=
      exists_nontrivial_subcontinuum_in_open hclosed.isCompact hconn hnt
        (mem_connectedComponentIn hx) hU hxU
    exact hno D hDcompact hDconn hxD
      (fun y hy => ⟨connectedComponentIn_subset F x (hDsub hy).1, (hDsub hy).2⟩) hDnt
  exact hsub.eq_singleton_of_mem (mem_connectedComponentIn hx)

/-- Adding compact totally disconnected dust preserves every singleton
component of a closed obstacle and gives singleton components off it. -/
theorem component_union_dust_eq_singleton
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F B : Set X} (hF : IsClosed F) (hB : IsClosed B)
    (htd : IsTotallyDisconnected B) {x : X} (hx : x ∈ F ∪ B)
    (hsing : x ∈ F → connectedComponentIn F x = {x}) :
    connectedComponentIn (F ∪ B) x = {x} := by
  let C := connectedComponentIn (F ∪ B) x
  have hclosed : IsClosed C := by
    change IsClosed (connectedComponentIn (F ∪ B) x)
    rw [connectedComponentIn_eq_image hx]
    exact (hF.union hB).isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hsub : C.Subsingleton := by
    by_contra hn
    have hnt : C.Nontrivial := Set.not_subsingleton_iff.mp hn
    have hCF : C ⊆ F := continuum_subset_closed_of_totallyDisconnected
      hclosed.isCompact hconn hnt hF htd (connectedComponentIn_subset (F ∪ B) x)
    have hCsing : C ⊆ {x} := by
      rw [← hsing (hCF hxC)]
      exact hconn.isPreconnected.subset_connectedComponentIn hxC hCF
    exact hn (fun _ ha _ hb => (mem_singleton_iff.mp (hCsing ha)).trans
      (mem_singleton_iff.mp (hCsing hb)).symm)
  exact hsub.eq_singleton_of_mem hxC

/-- Near a point, a finite closed level union only uses the levels which
contain that point. A singleton component in this smaller union is
therefore a singleton component in the entire union. -/
theorem component_finite_union_eq_singleton
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Finset ι) (H : ι → Set X) (hH : ∀ i ∈ s, IsClosed (H i))
    {x : X} (hx : x ∈ ⋃ i ∈ s, H i)
    (hpresent : connectedComponentIn (⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i) x = {x}) :
    connectedComponentIn (⋃ i ∈ s, H i) x = {x} := by
  classical
  let F := ⋃ i ∈ s, H i
  let B := ⋃ i ∈ s.filter (fun i => x ∉ H i), H i
  have hF : IsClosed F := isClosed_biUnion_finset (fun i hi => hH i hi)
  have hB : IsClosed B := isClosed_biUnion_finset (fun i hi => hH i (Finset.mem_filter.mp hi).1)
  have hxB : x ∉ B := by
    simp only [B, mem_iUnion, exists_prop, Finset.mem_filter]
    rintro ⟨i, ⟨_, hxi⟩, hxi'⟩
    exact hxi hxi'
  apply component_eq_singleton_of_local_no_continuum hF hx hB.isOpen_compl hxB
  intro D hDcompact hDconn hxD hDsub hDnt
  have hsub : D ⊆ ⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hDsub hy).1
    have hxi : x ∈ H i := by
      by_contra hn
      exact (hDsub hy).2 (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩, hyi⟩)
    exact mem_iUnion₂.mpr ⟨i, hi, mem_iUnion.mpr ⟨hxi, hyi⟩⟩
  have hsingle : D ⊆ {x} := by
    rw [← hpresent]
    exact hDconn.isPreconnected.subset_connectedComponentIn hxD hsub
  exact hDnt.not_subsingleton (fun _ ha _ hb => (mem_singleton_iff.mp (hsingle ha)).trans
    (mem_singleton_iff.mp (hsingle hb)).symm)

end CircleDomainRigidity

end OAI
