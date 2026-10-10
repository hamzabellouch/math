import OAI.Analysis.CircleDomains.Rigidity.MatchedComponentSides
import OAI.Analysis.CircleDomains.Topology.ExteriorSeparation
import OAI.Analysis.CircleDomains.Selection.EndCluster

namespace OAI

/-!
# Terminal components of an actual finite circle model

Every physical terminal disk determines a target complementary component.
The assignment exhausts all target components and respects every retained
Jordan contour. Only the existing topological inputs are used.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem SmoothJordanCore.boundary_subset_domain
    {G : Set Sphere} (C : SmoothJordanCore G) (i : Fin C.count) :
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i)) ⊆ G := by
  intro x hx
  apply C.subset
  have hxf : x ∈ frontier C.carrier := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    exact mem_iUnion.mpr ⟨i, hx⟩
  simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hxf

theorem jordan_address_eq_of_common_point
    {I : ℕ → Type*} (C : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (C n i))))
    {b d : (n : ℕ) → I n} {x : Sphere}
    (hb : x ∈ ⋂ n, closedTerminalCap (C n (b n)))
    (hd' : x ∈ ⋂ n, closedTerminalCap (C n (d n))) : b = d := by
  funext n
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n) (hd n) hne)
    (mem_iInter.mp hb n) (mem_iInter.mp hd' n)

theorem exists_finite_model_terminal_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ p : I → Sphere,
      (∀ i, p i ∈ Vᶜ) ∧
      Pairwise (Disjoint on fun i => connectedComponentIn Vᶜ (p i)) ∧
      (∀ y ∈ Vᶜ, ∃ i, connectedComponentIn Vᶜ y = connectedComponentIn Vᶜ (p i)) ∧
      (∀ i q, q ∈ closedTerminalCap (T i) → ∀ x : ℕ → Sphere,
        Tendsto x Filter.atTop (𝓝 q) → (∀ᶠ n in Filter.atTop, x n ∈ openCompletedRegion T) →
        ∀ y, Tendsto (f ∘ x) Filter.atTop (𝓝 y) → y ∈ connectedComponentIn Vᶜ (p i)) ∧
      ∀ A : SmoothJordanCore (openCompletedRegion T),
        ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
          (∀ j, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
            ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L j))) ∧
          ∀ i j, closedTerminalCap (T i) ⊆
            ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) →
            connectedComponentIn Vᶜ (p i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L j) := by
  classical
  let Q := openCompletedRegion T
  have hQ : IsOpen Q := isOpen_openCompletedRegion T
  have hQc : IsConnected Q := isConnected_openCompletedRegion T hTd
  have hQcomp : Qᶜ = ⋃ j, closedTerminalCap (T j) := compl_compl _
  have hinf : OnePoint.infty ∈ Q := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hcont : ContinuousOn f Q := fun x hx => (hf.smooth x hx).1.continuousWithinAt
  have hopen : ∀ S, IsOpen S → S ⊆ Q → IsOpen (f '' S) :=
    fun _ hS hSQ => hf.isOpen_image hV hS hSQ
  have hi : InjOn f Q := hf.bijOn.injOn
  have himage : f '' Q = V := hf.bijOn.image_eq
  have hcomponent {i : I} {q : Sphere} (hq : q ∈ closedTerminalCap (T i)) :
      connectedComponentIn Qᶜ q = closedTerminalCap (T i) := by
    rw [hQcomp]
    exact connectedComponentIn_finite_disjoint_closed _
      (fun j => (isCompact_closedTerminalCap (T j)).isClosed)
      (fun j => isPreconnected_closedTerminalCap (T j)) (disjoint_closedTerminalCaps T hTd) hq
  obtain ⟨C, J, hs, hc, hd, he, hb, hside⟩ :=
    exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies
      hQ hQc hinf hcont hopen hi hfix
  have hex (i : I) : ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere),
      p ∈ Vᶜ ∧ closedTerminalCap (T i) = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn Vᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    obtain ⟨q, hq⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hq⟩
    obtain ⟨b, p, hp, hsrc, htgt, hnest⟩ :=
      corresponding_target_end_of_source_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hqQ
    rw [hcomponent hq] at hsrc
    rw [himage] at hp htgt
    refine ⟨b, p, hp, hsrc, htgt, ?_⟩
    apply antitone_nat_of_succ_le
    intro n x hx
    have hn := (matched_jordan_disk_subset_iff hi
      ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1)))
      ((C (n + 1)).boundary_subset_domain _) (hb _ _) (hside _ _)).mpr (hnest n)
    obtain ⟨z, hz, hez⟩ := hn hx
    exact ⟨z, subset_closure hz, hez⟩
  choose b p hp hsrc htgt hanti using hex
  refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change x ∈ connectedComponentIn Vᶜ (p i) at hxi
    change x ∈ connectedComponentIn Vᶜ (p j) at hxj
    have hbij : b i = b j := jordan_address_eq_of_common_point J hd
      (htgt i ▸ hxi) (htgt j ▸ hxj)
    have hcaps : closedTerminalCap (T i) = closedTerminalCap (T j) := by
      rw [hsrc i, hsrc j, hbij]
    obtain ⟨z, hz⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hzj : z ∈ closedTerminalCap (T j) := by rwa [← hcaps]
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps T hTd hij) hz hzj
  · intro y hy
    have hy' : y ∈ (f '' Q)ᶜ := himage.symm ▸ hy
    obtain ⟨d, q, hq, hqsrc, hytgt, _⟩ :=
      corresponding_source_end_of_target_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hy'
    rw [hQcomp] at hq
    obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
    rw [hcomponent hqi] at hqsrc
    have hbd : b i = d := jordan_address_eq_of_common_point
      (fun n => (C n).disk) (fun n => (C n).disjoint)
      (hsrc i ▸ hqi) (hqsrc ▸ hqi)
    refine ⟨i, ?_⟩
    rw [← himage, hytgt, himage, htgt i, hbd]
  · intro i q hqi x hx hxQ y hy
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hqi⟩
    have hqside (n : ℕ) : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b i n)) :=
      (C n).omitted_point_mem_side hqQ (mem_iInter.mp (hsrc i ▸ hqi) n)
    have htgt' : connectedComponentIn (f '' Q)ᶜ (p i) = ⋂ n, closedTerminalCap (J n (b i n)) := by
      simpa only [himage] using htgt i
    simpa only [himage] using cluster_mem_corresponding_component
      (fun n => (C n).disk (b i n)) (fun n => J n (b i n))
      (fun n => hside n (b i n)) hqside htgt' hx hxQ hy
  · intro A
    obtain ⟨L, _, _, hboundary, hsideA⟩ :=
      exists_matched_image_core_of_continuous_open hschoenflies hQ hQc hinf
        hcont hopen hi hfix A
    refine ⟨L, hboundary, ?_⟩
    intro i j hij
    exact matched_component_subset_retained_side C J (b i) (hanti i) hb
      (hsrc i) (htgt i) (A.disk j) (L j) (hsideA j) hij

end CircleDomainRigidity

end

end OAI
