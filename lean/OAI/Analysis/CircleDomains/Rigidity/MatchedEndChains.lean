import OAI.Analysis.CircleDomains.Rigidity.MatchedImageCores
import OAI.Analysis.CircleDomains.Topology.JordanEndComponents

namespace OAI

/-!
# Refinement of matched source and target ends

A finer source contour lies on the chosen source side exactly when its
matched target contour lies on the corresponding target side. Filling
both Jordan contours upgrades boundary containment to strict closed-disk
containment.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem matched_jordan_disk_subset_iff
    {G : Set Sphere} {f : Sphere → Sphere} (hi : InjOn f G)
    (H₀ H₁ J₀ J₁ : ℂ ≃ₜ ℂ)
    (hfrontG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁) ⊆ G)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₁))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H₀)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀)) :
    (closedTerminalCap H₁ ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H₀) ↔
      (closedTerminalCap J₁ ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J₀) := by
  constructor
  · intro hsub
    apply image_mono
    apply closed_jordanInterior_subset_of_frontier_subset J₁ J₀
    intro z hz
    have hzimg : (z : Sphere) ∈ f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁)) := by
      rw [hboundary]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, hfx⟩ := hzimg
    have hxcap : x ∈ closedTerminalCap H₁ := by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, frontier_subset_closure hw, rfl⟩
    have hxside : f x ∈ f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀) := by
      rw [← hside]
      exact mem_image_of_mem _ ⟨hfrontG hx, hsub hxcap⟩
    have hzsphere : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior J₀ := hfx ▸ hxside.2
    exact OnePoint.coe_injective.mem_set_image.mp hzsphere
  · intro hsub
    apply image_mono
    apply closed_jordanInterior_subset_of_frontier_subset H₁ H₀
    intro z hz
    have hzG := hfrontG (mem_image_of_mem _ hz)
    have hzfront : f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₁) := by
      rw [← hboundary]
      exact mem_image_of_mem _ (mem_image_of_mem _ hz)
    have hzcap : f (z : Sphere) ∈ closedTerminalCap J₁ := by
      obtain ⟨w, hw, he⟩ := hzfront
      exact ⟨w, frontier_subset_closure hw, he⟩
    have hzside : f (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H₀)) := by
      rw [hside]
      exact ⟨mem_image_of_mem _ hzG, hsub hzcap⟩
    obtain ⟨w, hw, he⟩ := hzside
    have hwz : w = (z : Sphere) := hi hw.1 hzG he
    exact OnePoint.coe_injective.mem_set_image.mp (hwz ▸ hw.2)

end CircleDomainRigidity

end

end OAI
