import OAI.Analysis.CircleDomains.Selection.CollapseRelation

namespace OAI

/-!
# Boundary bumping for compact continua

This is the compact-space argument used in the small-disk and generic-level
lemmas of the uniformization manuscript. It does not assume local
connectedness of the continuum.
-/

open Set Topology

namespace CircleDomainRigidity

/-- Every component of a proper closed subset of a compact connected space
meets its boundary. -/
theorem component_meets_frontier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ)
    {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hnonempty
  have hdisj : Disjoint (frontier F) (connectedComponentIn F x) :=
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnonempty)).symm
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  let K : Set F := (Subtype.val : F → X) ⁻¹' frontier F
  have hK : IsClosed K := isClosed_frontier.preimage continuous_subtype_val
  have hd : Disjoint K (connectedComponent xf) := by
    apply Set.disjoint_left.mpr
    intro z hzK hzC
    apply Set.disjoint_left.mp hdisj hzK
    rw [connectedComponentIn_eq_image hx]
    exact ⟨z, hzC, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen xf] at hd
  obtain ⟨s, hs⟩ := hK.isCompact.elim_finite_subfamily_closed
    (fun U : {U : Set F // IsClopen U ∧ xf ∈ U} => U.val)
    (fun U => U.property.1.isClosed) hd
  let U : Set F := ⋂ V ∈ s, (V : Set F)
  have hU : IsClopen U := isClopen_biInter_finset fun V _ => V.property.1
  have hxU : xf ∈ U := mem_iInter₂.mpr fun V _ => V.property.2
  let W : Set X := (Subtype.val : F → X) '' U
  have hWclosed : IsClosed W := hF.isClosedMap_subtype_val U hU.isClosed
  have hWF : W ⊆ F := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hWint : W ⊆ interior F := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hzi
    have hzK : z ∈ K := ⟨subset_closure z.property, hzi⟩
    exact Set.disjoint_left.mp hs hzK hz
  obtain ⟨O, hO, hWO⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hU.isOpen
  change W = O ∩ range (Subtype.val : F → X) at hWO
  have hWeq : W = O ∩ interior F := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨(hWO ▸ hz).1, hWint hz⟩
    · intro z hz
      rw [hWO]
      exact ⟨hz.1, ⟨⟨z, interior_subset hz.2⟩, rfl⟩⟩
  have hWopen : IsOpen W := hWeq ▸ hO.inter isOpen_interior
  have hWuniv : W = univ := (show IsClopen W from ⟨hWclosed, hWopen⟩).eq_univ
    ⟨x, xf, hxU, rfl⟩
  apply hproper
  apply Set.eq_univ_of_univ_subset
  rw [← hWuniv]
  exact hWF

/-- Adjoining totally disconnected dust to a closed set creates no new
nondegenerate continuum. This is the first small-disk lemma of the paper. -/
theorem continuum_subset_closed_of_totallyDisconnected
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C F B : Set X} (hC : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) (hF : IsClosed F) (hB : IsTotallyDisconnected B)
    (hsub : C ⊆ F ∪ B) : C ⊆ F := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  intro x hx
  by_contra hxF
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := ((Subtype.val : C → X) ⁻¹' F)ᶜ ∩ {yc}ᶜ
  have hO : IsOpen O := (hF.preimage continuous_subtype_val).isOpen_compl.inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxF, fun h => hyx (congrArg Subtype.val h).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro h
    have hyN : yc ∈ N := by rw [h]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hzC, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  have hconnN : IsPreconnected (connectedComponentIn N xc) :=
    isPreconnected_connectedComponentIn
  have himageB : (Subtype.val : C → X) '' connectedComponentIn N xc ⊆ B := by
    rintro _ ⟨w, hw, rfl⟩
    have hwN := connectedComponentIn_subset N xc hw
    exact (hsub w.property).resolve_left (hNO hwN).1
  have hsingle := hB _ himageB (hconnN.image _ continuous_subtype_val.continuousOn)
  have hzxeq : z.val = x := hsingle ⟨z, hzC, rfl⟩
    ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzxc : z = xc := Subtype.ext hzxeq
  have hxfront : xc ∈ frontier N := hzxc ▸ hzfront
  exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)

end CircleDomainRigidity

end OAI
