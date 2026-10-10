import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcSystems
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedDomain

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ} {D : Finset (Vertex M)}

theorem localIce_add_of_disjoint (q r : Edge M →₀ ℤ) (v : Vertex M)
    (hq : LocalIce q v) (hr : LocalIce r v) (hd : v∉activeSites q ∨ v∉activeSites r) : LocalIce (q+r) v := by
  rcases hd with hq0 | hr0
  · have hz : ∀k,orientedFlow q (v,k)=0 := by simpa only [mem_activeSites,not_exists,not_not] using hq0
    simpa only [LocalIce,map_add,Finsupp.add_apply,hz,zero_add] using hr
  · have hz : ∀k,orientedFlow r (v,k)=0 := by simpa only [mem_activeSites,not_exists,not_not] using hr0
    simpa only [LocalIce,map_add,Finsupp.add_apply,hz,add_zero] using hq

theorem active_add_disjoint_on (D : Finset (Vertex M)) (q r : Edge M →₀ ℤ)
    (hd : Disjoint (D∩activeSites q) (D∩activeSites r)) :
    D∩activeSites (q+r)=(D∩activeSites q)∪(D∩activeSites r) := by
  ext v
  simp only [Finset.mem_inter,Finset.mem_union,mem_activeSites,map_add,Finsupp.add_apply]
  constructor
  · rintro ⟨hv,k,hk⟩
    by_cases hq : orientedFlow q (v,k)=0
    · exact Or.inr ⟨hv,k,by simpa only [hq,zero_add] using hk⟩
    · exact Or.inl ⟨hv,k,hq⟩
  · rintro (⟨hv,k,hk⟩ | ⟨hv,k,hk⟩)
    · have hr : v∉activeSites r := fun hh => Finset.disjoint_left.mp hd
        (Finset.mem_inter.mpr ⟨hv,(mem_activeSites q v).mpr ⟨k,hk⟩⟩) (Finset.mem_inter.mpr ⟨hv,hh⟩)
      have hz : orientedFlow r (v,k)=0 := by
        by_contra hn; exact hr ((mem_activeSites r v).mpr ⟨k,hn⟩)
      exact ⟨hv,k,by simpa only [hz,add_zero] using hk⟩
    · have hq : v∉activeSites q := fun hh => Finset.disjoint_left.mp hd
        (Finset.mem_inter.mpr ⟨hv,hh⟩) (Finset.mem_inter.mpr ⟨hv,(mem_activeSites r v).mpr ⟨k,hk⟩⟩)
      have hz : orientedFlow q (v,k)=0 := by
        by_contra hn; exact hq ((mem_activeSites q v).mpr ⟨k,hn⟩)
      exact ⟨hv,k,by simpa only [hz,zero_add] using hk⟩

abbrev ArcClosedData (D : Finset (Vertex M)) := (S : ArcSystem D) × ClosedDomainFlow (D\S.vertices)

namespace ArcClosedData
variable (B : ArcClosedData D)
noncomputable def current : Edge M →₀ ℤ := B.1.current+B.2.val.val

theorem closed_subset : activeSites B.2.val.val⊆D := B.2.property.trans Finset.sdiff_subset

theorem disjoint_closed : Disjoint B.1.vertices (activeSites B.2.val.val) := by
  exact Finset.disjoint_left.mpr (fun _ hv hr => (Finset.mem_sdiff.mp (B.2.property hr)).2 hv)

theorem domain_disjoint : Disjoint (D∩activeSites B.1.current) (D∩activeSites B.2.val.val) := by
  rw [B.1.domain_active,Finset.inter_eq_right.mpr B.closed_subset]
  exact B.disjoint_closed

theorem domain_active : D∩activeSites B.current=B.1.vertices∪activeSites B.2.val.val := by
  rw [current,active_add_disjoint_on D _ _ B.domain_disjoint,B.1.domain_active,
    Finset.inter_eq_right.mpr B.closed_subset]

theorem local_ice (v : Vertex M) (hv : v∈D) : LocalIce B.current v := by
  apply localIce_add_of_disjoint B.1.current B.2.val.val v (B.1.local_ice v hv) (B.2.val.property v)
  by_cases hq : v∈activeSites B.1.current
  · right
    intro hr
    exact Finset.disjoint_left.mp B.domain_disjoint (Finset.mem_inter.mpr ⟨hv,hq⟩) (Finset.mem_inter.mpr ⟨hv,hr⟩)
  · exact Or.inl hq

theorem supported : SupportedAt D B.current := by
  intro g hg hr
  have hc : orientedFlow B.2.val.val g=0 := by
    by_contra hh
    exact hg (B.closed_subset ((mem_activeSites B.2.val.val g.1).mpr ⟨g.2,hh⟩))
  simp only [current,map_add,Finsupp.add_apply,B.1.supported g hg hr,hc,add_zero]

private theorem list_pairwise {α : Type*} {R : α → α → Prop} (L : List α) (hn : L.Nodup)
    (hR : ∀a∈L,∀b∈L,a≠b → R a b) : L.Pairwise R := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hn
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih hn.2 (fun b hb c hc hbc => hR b (by simp [hb]) c (by simp [hc]) hbc)⟩
    intro b hb
    exact hR a (by simp) b (by simp [hb]) (fun he => hn.1 (he ▸ hb))

 

noncomputable def decomposition : BoundaryDecomposition D B.current where
  arcs:=B.1.val.toList
  closed:=B.2.val.val
  reconstruction:=by
    have he:=List.sum_toFinset BoundaryArc.current B.1.val.nodup_toList
    simp only [Finset.toList_toFinset] at he
    exact congrArg (fun q : Edge M →₀ ℤ => q+B.2.val.val) he
  ice:=B.2.val.property
  contained:=B.closed_subset
  pairwise:=list_pairwise _ B.1.val.nodup_toList (by
    intro A hA C hC hAC
    exact B.1.property (Finset.mem_toList.mp hA) (Finset.mem_toList.mp hC) hAC)
  disjoint_closed:=by
    intro A hA
    exact B.disjoint_closed.mono_left (Finset.subset_biUnion_of_mem BoundaryArc.vertices (Finset.mem_toList.mp hA))
  arcs_active:=by
    intro A hA v hv
    change v∈activeSites B.current∩D
    rw [Finset.inter_comm,B.domain_active]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨A,Finset.mem_toList.mp hA,hv⟩)
  closed_active:=by
    intro v hv
    change v∈activeSites B.current∩D
    rw [Finset.inter_comm,B.domain_active]
    exact Finset.mem_union_right _ hv

theorem weight_factor : domainWeight D B.current=B.1.weight*uniformSeamWeight B.2.val.val := by
  rw [current,domainWeight_add D _ _ B.domain_disjoint,B.1.domain_weight,
    domainWeight_closed D _ B.2.val.property B.closed_subset]
end ArcClosedData
end PolynomialVacuumCylinder

end OAI
