import OAI.Analysis.CircleDomains.Topology.ProjectionJordanCap
import Mathlib.Topology.Connected.TotallyDisconnected

namespace OAI

/-! The fibers of the continuous inverse projection are the complementary
components when the original complement is dust, by the matched Jordan
exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_component_eq_fiber
    {G : Set Sphere} (hG : IsOpen G) (hTD : IsTotallyDisconnected Gᶜ)
    {f P : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hP : Continuous P) (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n+1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    connectedComponentIn (f '' G)ᶜ p = P ⁻¹' {P p} := by
  have hfront (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hh : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
  have hcap (n : ℕ) (i : Fin (C n).count) := inverse_projection_matched_cap hG hP hInv hOut
    ((C n).disk i) (J n i) (hfront n i) (hboundary n i) (hside n i)
  have hvalue (b : (n : ℕ) → Fin (C n).count) (q : Sphere) (hq : q ∈ Gᶜ)
      (hs : connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)))
      {z : Sphere} (hz : z ∈ ⋂ n, closedTerminalCap (J n (b n))) : P z = q := by
    have hmem : P z ∈ connectedComponentIn Gᶜ q := by
      rw [hs]
      exact mem_iInter.mpr fun n => hcap n (b n) (mem_image_of_mem P (mem_iInter.mp hz n))
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem
  obtain ⟨b, q, hq, hs, ht, _⟩ := corresponding_source_end_of_target hG hf hi C J
    hstrict hcover hJd hJe hboundary hside hp
  have hpp : P p = q := hvalue b q hq hs (ht ▸ mem_connectedComponentIn hp)
  apply Subset.antisymm
  · intro z hz
    change P z = P p
    exact (hvalue b q hq hs (ht ▸ hz)).trans hpp.symm
  · intro z hz
    have he : P z = P p := hz
    have hzOut : z ∈ (f '' G)ᶜ := by
      rintro ⟨x, hx, rfl⟩
      exact hOut p hp (by rw [← he, hInv x hx]; exact hx)
    obtain ⟨b', q', hq', hs', ht', _⟩ := corresponding_source_end_of_target hG hf hi C J
      hstrict hcover hJd hJe hboundary hside hzOut
    have hqq : q' = q := (hvalue b' q' hq' hs' (ht' ▸ mem_connectedComponentIn hzOut)).symm.trans
      (he.trans hpp)
    have hb : b' = b := by
      funext n
      by_contra hne
      have hq₁ : q ∈ closedTerminalCap ((C n).disk (b n)) :=
        mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n
      have hq₂ : q ∈ closedTerminalCap ((C n).disk (b' n)) := by
        rw [← hqq]
        exact mem_iInter.mp (hs' ▸ mem_connectedComponentIn hq') n
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n).disk (C n).disjoint hne) hq₂ hq₁
    rw [ht]
    rw [hb] at ht'
    exact ht' ▸ mem_connectedComponentIn hzOut

end CircleDomainRigidity

end

end OAI
