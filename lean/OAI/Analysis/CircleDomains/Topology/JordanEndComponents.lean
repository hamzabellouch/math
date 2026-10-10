import OAI.Analysis.CircleDomains.Topology.ClosedJordanCore
import OAI.Analysis.CircleDomains.Topology.NestedEndComponents

namespace OAI

/-!
# End components of a strict Jordan-core exhaustion

The selected target disk at each level is determined by the omitted point.
Strict core inclusion forces these disks to nest strictly. Their intersection
is exactly the full complementary component of the exhausted image.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem component_eq_nested_jordan_end
    {I : ℕ → Type*} [∀ n, Finite (I n)]
    (H : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (H n i))))
    (A : ℕ → Set Sphere) {V : Set Sphere}
    (hA : ∀ n, (A n)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H n i))
    (hstrict : ∀ n, A n ⊆ interior (A (n + 1))) (hcover : (⋃ n, A n) = V)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ b : (n : ℕ) → I n,
      connectedComponentIn Vᶜ p = ⋂ n, closedTerminalCap (H n (b n)) ∧
      (∀ n, closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n))) ∧
      ∀ n, connectedComponentIn Vᶜ p ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n)) := by
  classical
  have hAV (n : ℕ) : A n ⊆ V := by rw [← hcover]; exact subset_iUnion A n
  have hAe (n : ℕ) : A n = closedJordanCore (H n) := by
    apply compl_injective
    simpa only [closedJordanCore, compl_compl] using hA n
  have hcap (n : ℕ) (i : I n) : closedTerminalCap (H n i) ⊆ (interior (A n))ᶜ := by
    rw [hAe n, interior_closedJordanCore]
    intro q hq hqint
    exact hqint (mem_iUnion.mpr ⟨i, hq⟩)
  have hCclosed (n : ℕ) (i : I n) : IsClosed (closedTerminalCap (H n i)) :=
    (isCompact_closedTerminalCap (H n i)).isClosed
  have hCd (n : ℕ) : Pairwise (Disjoint on fun i => closedTerminalCap (H n i)) :=
    disjoint_closedTerminalCaps (H n) (hd n)
  have hCcover (n : ℕ) : Vᶜ ⊆ ⋃ i, closedTerminalCap (H n i) := by
    intro q hq
    have hqa : q ∈ (A n)ᶜ := fun h => hq (hAV n h)
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hA n ▸ hqa)
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩
  have hpopen (n : ℕ) : ∃ i : I n, p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H n i) := by
    have hpa : p ∈ (A n)ᶜ := fun h => hp (hAV n h)
    exact mem_iUnion.mp (hA n ▸ hpa)
  choose b hb using hpopen
  have hpb (n : ℕ) : p ∈ closedTerminalCap (H n (b n)) := by
    obtain ⟨z, hz, he⟩ := hb n
    exact ⟨z, subset_closure hz, he⟩
  have hsmall (n : ℕ) : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆ (A n)ᶜ := by
    intro q hq hqa
    exact hcap (n + 1) (b (n + 1)) hq (hstrict n hqa)
  have hnest (n : ℕ) : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n)) := by
    have hsub : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
        ⋃ i, closedTerminalCap (H n i) := by
      intro q hq
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hA n ▸ hsmall n hq)
      exact mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩
    have hpiece := connectedComponentIn_subset_finite_closed_piece
      (fun i => closedTerminalCap (H n i)) (hCclosed n) (hCd n) hsub (hpb (n + 1)) (hpb n)
    have hconnected := (isPreconnected_closedTerminalCap (H (n + 1) (b (n + 1)))).subset_connectedComponentIn
      (hpb (n + 1)) (Subset.refl _)
    intro q hq
    have hqold := hpiece (hconnected hq)
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp (hA n ▸ hsmall n hq)
    have hqi : q ∈ closedTerminalCap (H n i) := ⟨z, subset_closure hz, he⟩
    by_cases hi : i = b n
    · exact hi ▸ ⟨z, hz, he⟩
    · exact (Set.disjoint_left.mp (hCd n hi) hqi hqold).elim
  have hanti : Antitone (fun n => closedTerminalCap (H n (b n))) := by
    apply antitone_nat_of_succ_le
    intro n q hq
    obtain ⟨z, hz, he⟩ := hnest n hq
    exact ⟨z, subset_closure hz, he⟩
  have hmiss : (⋂ n, closedTerminalCap (H n (b n))) ⊆ Vᶜ := by
    intro q hq hqV
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hqV)
    exact hsmall n (mem_iInter.mp hq (n + 1)) hn
  have he := connectedComponentIn_eq_nested_end
    (fun n i => closedTerminalCap (H n i)) b hCclosed
    (fun n => ⟨⟨p, hpb n⟩, isPreconnected_closedTerminalCap (H n (b n))⟩)
    hCd hCcover hanti hmiss (mem_iInter.mpr hpb)
  refine ⟨b, he, hnest, ?_⟩
  intro n
  rw [he]
  exact (iInter_subset _ (n + 1)).trans (hnest n)

end CircleDomainRigidity

end

end OAI
