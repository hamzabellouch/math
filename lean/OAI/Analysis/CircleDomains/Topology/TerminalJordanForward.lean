import OAI.Analysis.CircleDomains.Topology.TerminalJordanSide

namespace OAI

/-! The converse collar incidence: a source terminal in the retained
bounded side has its assigned target component in the target bounded side. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.target_inside_of_source_inside
    {I : Type*} [Finite I] {T : I → ℂ ≃ₜ ℂ}
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (_hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (H J : ℂ ≃ₜ ℂ)
    (hbdJ : ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ⊆ V)
    (hside : f '' (openCompletedRegion T ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (i : I) (hin : closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    connectedComponentIn Vᶜ (a.point i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hav : Disjoint (connectedComponentIn Vᶜ (a.point i)) (frontier A) := by
    exact Set.disjoint_left.mpr (fun _ h h' =>
      connectedComponentIn_subset _ _ h (hbdJ (hAf ▸ h')))
  obtain ⟨q, hq⟩ := (isConnected_frontier_jordanInterior (T i)).nonempty
  have hqcap : (q : Sphere) ∈ closedTerminalCap (T i) := ⟨q, frontier_subset_closure hq, rfl⟩
  have hqcl : (q : Sphere) ∈ closure (openCompletedRegion T) := by
    rw [← interior_closedJordanCore, closure_interior_closedJordanCore T hTd]
    intro hu
    obtain ⟨j, z, hz, he⟩ := mem_iUnion.mp hu
    have hzq := OnePoint.coe_injective he
    subst z
    by_cases hji : j = i
    · subst j
      exact hq.2 ((jordanInterior_isOpen (T i)).interior_eq.symm ▸ hz)
    · exact Set.disjoint_left.mp (hTd hji) (subset_closure hz) (frontier_subset_closure hq)
  obtain ⟨x, hxQ, hx⟩ := mem_closure_iff_seq_limit.mp hqcl
  obtain ⟨y, _, s, hs, hy⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (f (x n)))
  have hys : y ∈ connectedComponentIn Vᶜ (a.point i) :=
    a.cluster i (q : Sphere) hqcap (x ∘ s) (hx.comp hs.tendsto_atTop)
      (Eventually.of_forall fun n => hxQ (s n)) y hy
  have hxH : ∀ᶠ n in atTop, x (s n) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H :=
    (hx.comp hs.tendsto_atTop).eventually
      ((OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)).mem_nhds (hin hqcap))
  have hycl : y ∈ closure A := by
    apply mem_closure_of_tendsto hy
    filter_upwards [hxH] with n hn
    have hh : f (x (s n)) ∈ V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
      rw [← hside]
      exact mem_image_of_mem f ⟨hxQ (s n), hn⟩
    exact hh.2
  have hyA : y ∈ A := by
    by_contra hn
    exact Set.disjoint_left.mp hav hys ⟨hycl, hAo.interior_eq.symm ▸ hn⟩
  have hcover : connectedComponentIn Vᶜ (a.point i) ⊆ A ∪ (closure A)ᶜ := by
    intro z hz
    by_cases hza : z ∈ A
    · exact Or.inl hza
    · exact Or.inr (fun hc => Set.disjoint_left.mp hav hz ⟨hc, hAo.interior_eq.symm ▸ hza⟩)
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hAo
    isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hcover ⟨y, hys, hyA⟩

end CircleDomainRigidity

end

end OAI
