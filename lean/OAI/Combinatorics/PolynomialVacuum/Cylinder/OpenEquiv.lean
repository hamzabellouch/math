import OAI.Combinatorics.PolynomialVacuum.Cylinder.CombinedArcs
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackEquiv

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]
omit [NeZero M] in
private theorem arcs_unique_of_eq {D : Finset (Vertex M)} {q r : Edge M →₀ ℤ}
    (B : BoundaryDecomposition D q) (C : BoundaryDecomposition D r) (he : q=r) :
    B.arcs.toFinset=C.arcs.toFinset := by
  subst r
  exact B.arcs_unique C
namespace ArcClosedData
variable {D : Finset (Vertex M)}

omit [NeZero M] in
theorem current_injective : Function.Injective (current (D:=D)) := by
  intro B C he
  have hs : B.1.val=C.1.val := by
    have hh:=arcs_unique_of_eq B.decomposition C.decomposition he
    simpa only [decomposition,Finset.toList_toFinset] using hh
  have hs' : B.1=C.1 := Subtype.ext hs
  cases B with
  | mk S q =>
    cases C with
    | mk T r =>
      dsimp only at hs'
      subst T
      have hqr : q=r := by
        apply Subtype.ext
        apply Subtype.ext
        exact add_left_cancel he
      cases hqr
      rfl

omit [NeZero M] in
theorem exists_of_flow (q : Edge M →₀ ℤ) (hi : ∀v∈D,LocalIce q v) (hs : SupportedAt D q) :
    ∃B : ArcClosedData D,B.current=q := by
  obtain ⟨B⟩:=boundary_decomposition D q hi hs
  let S : ArcSystem D:=⟨B.arcs.toFinset,
    (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint B.arcs_nodup).mpr B.pairwise⟩
  have hclosed : activeSites B.closed⊆D\S.vertices := by
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨B.contained hv,?_⟩
    intro hh
    obtain ⟨A,hA,hvA⟩:=Finset.mem_biUnion.mp hh
    exact Finset.disjoint_left.mp (B.disjoint_closed A (List.mem_toFinset.mp hA)) hvA hv
  refine ⟨⟨S,⟨⟨B.closed,B.ice⟩,hclosed⟩⟩,?_⟩
  change S.current+B.closed=q
  apply Eq.trans _ B.reconstruction.symm
  exact congrArg (fun r : Edge M →₀ ℤ => r+B.closed) (List.sum_toFinset BoundaryArc.current B.arcs_nodup)
end ArcClosedData

noncomputable def openFlowEquiv : ArcClosedData (bandSites M H) ≃ BandFlow M H :=
  Equiv.ofBijective (fun B=>⟨B.current,B.local_ice,B.supported⟩) ⟨by
    intro B C he
    exact ArcClosedData.current_injective (congrArg Subtype.val he),by
    intro q
    obtain ⟨B,hB⟩:=ArcClosedData.exists_of_flow q.val q.property.1 q.property.2
    exact ⟨B,Subtype.ext hB⟩⟩

 

theorem band_partition_arcs :
    (∑q : BandFlow M H,domainWeight (bandSites M H) q.val)=
      ∑S : ArcSystem (bandSites M H),S.weight := by
  rw [← (openFlowEquiv (M:=M) (H:=H)).sum_comp]
  change (∑B : ArcClosedData (bandSites M H),domainWeight (bandSites M H) B.current)=_
  simp_rw [ArcClosedData.weight_factor]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  change (∑y : ClosedDomainFlow _,S.weight*uniformSeamWeight y.val.val)=_
  rw [← Finset.mul_sum,closed_domain_partition_one,mul_one]

end PolynomialVacuumCylinder

end OAI
