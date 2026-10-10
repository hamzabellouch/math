import OAI.Analysis.CircleDomains.Transfer.SourceTargetEnds

namespace OAI

/-!
# Cluster values at a specified end

The matched side identity places images of a sequence approaching the
source end eventually in every target collar. A convergent image sequence
therefore limits in the full target component, without extending the map
across that component.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

theorem cluster_mem_matched_end
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ ⋂ j, closedTerminalCap (J j) := by
  apply mem_iInter.mpr
  intro j
  have hevent : ∀ᶠ n in atTop, x n ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j) :=
    hx.eventually ((OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).mem_nhds (hq j))
  apply (isCompact_closedTerminalCap (J j)).isClosed.mem_of_tendsto hy
  filter_upwards [hevent, hxG] with n hn hnG
  have hfn : f (x n) ∈ f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)) := by
    rw [← hside j]
    exact mem_image_of_mem _ ⟨hnG, hn⟩
  obtain ⟨z, hz, he⟩ := hfn.2
  exact ⟨z, subset_closure hz, he⟩

theorem cluster_mem_corresponding_component
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p p₀ : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    (hcomponent : connectedComponentIn (f '' G)ᶜ p₀ = ⋂ j, closedTerminalCap (J j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ connectedComponentIn (f '' G)ᶜ p₀ := by
  rw [hcomponent]
  exact cluster_mem_matched_end H J hside hq hx hxG hy

end CircleDomainRigidity

end OAI
