import OAI.Analysis.CircleDomains.Rigidity.MatchedEndChains

namespace OAI

/-!
# A target component corresponding to a source component

For the same sequence of matched boundary labels, the nested source disks
intersect in the original complementary component and the nested target
disks intersect in a full target complementary component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem corresponding_target_end_of_source_of_continuous_open
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere), p ∈ (f '' G)ᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) := by
  have hcarriercover : (⋃ n, (C n).carrier) = G := by
    apply Subset.antisymm (iUnion_subset fun n => (C n).subset)
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    exact mem_iUnion.mpr ⟨n, interior_subset hn⟩
  obtain ⟨b, hb, hsourcenest, _⟩ := component_eq_nested_jordan_end
    (fun n => (C n).disk) (fun n => (C n).disjoint) (fun n => (C n).carrier)
    (fun _ => compl_compl _) hstrict hcarriercover hq
  have hfrontG (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxfront : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxfront
  have htargetnest (n : ℕ) : closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) :=
    (matched_jordan_disk_subset_iff hi ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1))) (hfrontG _ _) (hboundary _ _) (hside _ _)).mp
      (hsourcenest n)
  have hanti : Antitone (fun n => closedTerminalCap (J n (b n))) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    obtain ⟨z, hz, he⟩ := htargetnest n hx
    exact ⟨z, subset_closure hz, he⟩
  have hclosed (n : ℕ) (i : Fin (C n).count) : IsClosed (closedTerminalCap (J n i)) :=
    (isCompact_closedTerminalCap (J n i)).isClosed
  have hconnected (n : ℕ) : IsConnected (closedTerminalCap (J n (b n))) :=
    ⟨(nontrivial_closedTerminalCap (J n (b n))).nonempty,
      isPreconnected_closedTerminalCap (J n (b n))⟩
  have hnonempty := (isConnected_nested_sphere_intersection (fun n => hclosed n (b n)) hconnected hanti).nonempty
  obtain ⟨p, hp⟩ := hnonempty
  have hAe (n : ℕ) : f '' (C n).carrier = closedJordanCore (J n) := by
    apply compl_injective
    simpa only [closedJordanCore, compl_compl] using hJe n
  have hcap (n : ℕ) (i : Fin (C n).count) :
      closedTerminalCap (J n i) ⊆ (interior (f '' (C n).carrier))ᶜ := by
    rw [hAe n, interior_closedJordanCore]
    intro x hx hxint
    exact hxint (mem_iUnion.mpr ⟨i, hx⟩)
  have hmiss : (⋂ n, closedTerminalCap (J n (b n))) ⊆ (f '' G)ᶜ := by
    rintro x hx ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hy)
    apply hcap n (b n) (mem_iInter.mp hx n)
    rw [interior_image_of_continuous_open hf ho hG hi (C n).subset]
    exact mem_image_of_mem _ hn
  have hEcover (n : ℕ) : (f '' G)ᶜ ⊆ ⋃ i, closedTerminalCap (J n i) := by
    intro x hx
    have hxa : x ∈ (f '' (C n).carrier)ᶜ := fun h => hx (image_mono (C n).subset h)
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp (hJe n ▸ hxa)
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, he⟩
  have hcomponent := connectedComponentIn_eq_nested_end (fun n i => closedTerminalCap (J n i)) b
    hclosed hconnected (fun n => disjoint_closedTerminalCaps (J n) (hJd n)) hEcover hanti hmiss hp
  exact ⟨b, p, hmiss hp, hb, hcomponent, htargetnest⟩

theorem corresponding_target_end_of_source
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere), p ∈ (f '' G)ᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) :=
  corresponding_target_end_of_source_of_continuous_open hG
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi C J hstrict hcover hJd hJe hboundary hside hq


/-- Conversely every target complementary component has a source component
with the same matched boundary address. -/
theorem corresponding_source_end_of_target_of_continuous_open
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere), q ∈ Gᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) := by
  have hAstrict (n : ℕ) : f '' (C n).carrier ⊆ interior (f '' (C (n + 1)).carrier) := by
    rw [interior_image_of_continuous_open hf ho hG hi (C (n + 1)).subset]
    exact image_mono (hstrict n)
  have hAcover : (⋃ n, f '' (C n).carrier) = f '' G := by
    apply Subset.antisymm (iUnion_subset fun n => image_mono (C n).subset)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    exact mem_iUnion.mpr ⟨n, x, interior_subset hn, rfl⟩
  obtain ⟨b, hb, htargetnest, _⟩ := component_eq_nested_jordan_end J hJd
    (fun n => f '' (C n).carrier) hJe hAstrict hAcover hp
  have hfrontG (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxfront : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxfront
  have hsourcenest (n : ℕ) : closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) :=
    (matched_jordan_disk_subset_iff hi ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1))) (hfrontG _ _) (hboundary _ _) (hside _ _)).mpr
      (htargetnest n)
  have hanti : Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    obtain ⟨z, hz, he⟩ := hsourcenest n hx
    exact ⟨z, subset_closure hz, he⟩
  have hclosed (n : ℕ) (i : Fin (C n).count) : IsClosed (closedTerminalCap ((C n).disk i)) :=
    (isCompact_closedTerminalCap ((C n).disk i)).isClosed
  have hconnected (n : ℕ) : IsConnected (closedTerminalCap ((C n).disk (b n))) :=
    ⟨(nontrivial_closedTerminalCap ((C n).disk (b n))).nonempty,
      isPreconnected_closedTerminalCap ((C n).disk (b n))⟩
  obtain ⟨q, hq⟩ := (isConnected_nested_sphere_intersection
    (fun n => hclosed n (b n)) hconnected hanti).nonempty
  have hmiss : (⋂ n, closedTerminalCap ((C n).disk (b n))) ⊆ Gᶜ := by
    intro x hx hxG
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hxG)
    rw [SmoothJordanCore.carrier, interior_closedJordanCore] at hn
    exact hn (mem_iUnion.mpr ⟨b n, mem_iInter.mp hx n⟩)
  have hEcover (n : ℕ) : Gᶜ ⊆ ⋃ i, closedTerminalCap ((C n).disk i) := by
    intro x hx
    have hxa : x ∉ (C n).carrier := fun h => hx ((C n).subset h)
    have hxU : x ∈ ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i) := not_not.mp hxa
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, he⟩
  have hcomponent := connectedComponentIn_eq_nested_end
    (fun n i => closedTerminalCap ((C n).disk i)) b hclosed hconnected
    (fun n => disjoint_closedTerminalCaps (C n).disk (C n).disjoint) hEcover hanti hmiss hq
  exact ⟨b, q, hmiss hq, hcomponent, hb, hsourcenest⟩

theorem corresponding_source_end_of_target
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere), q ∈ Gᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) :=
  corresponding_source_end_of_target_of_continuous_open hG
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi C J hstrict hcover hJd hJe hboundary hside hp


/-- The constructed smooth exhaustion gives every complementary component on
either side a matched source/target address. Only the previously used Sard,
one-manifold classification and Schoenflies inputs enter the construction. -/
theorem exists_matched_component_exhaustion_of_continuous_open
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ q ∈ Gᶜ, ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere),
        p ∈ (f '' G)ᶜ ∧
        connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
        connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n))) ∧
      (∀ p ∈ (f '' G)ᶜ, ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere),
        q ∈ Gᶜ ∧
        connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
        connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n))) := by
  obtain ⟨C, J, hs, hc, hd, he, hb, hi'⟩ :=
    exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies hG hconn hinf hf ho hi hfix
  refine ⟨C, J, hs, hc, ?_, ?_⟩
  · intro q hq
    obtain ⟨b, p, hp, hsource, htarget, _⟩ :=
      corresponding_target_end_of_source_of_continuous_open hG hf ho hi C J hs hc hd he hb hi' hq
    exact ⟨b, p, hp, hsource, htarget⟩
  · intro p hp
    obtain ⟨b, q, hq, hsource, htarget, _⟩ :=
      corresponding_source_end_of_target_of_continuous_open hG hf ho hi C J hs hc hd he hb hi' hp
    exact ⟨b, q, hq, hsource, htarget⟩

theorem exists_matched_component_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ q ∈ Gᶜ, ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere),
        p ∈ (f '' G)ᶜ ∧
        connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
        connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n))) ∧
      (∀ p ∈ (f '' G)ᶜ, ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere),
        q ∈ Gᶜ ∧
        connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
        connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n))) :=
  exists_matched_component_exhaustion_of_continuous_open hsard hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix


end CircleDomainRigidity

end

end OAI
