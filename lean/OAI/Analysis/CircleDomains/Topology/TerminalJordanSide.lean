import OAI.Analysis.CircleDomains.Topology.RetainedImageBoundary
import OAI.Analysis.CircleDomains.Reflection.RoundExteriorPoint

namespace OAI

/-! A target hole inside a retained image collar comes from a source
terminal inside the original collar. The inverse boundary-neighborhood
theorem proves this without a boundary extension. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.source_inside_of_target_inside
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T)
    (hside : f '' (openCompletedRegion T ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (i : I) (hin : closedBall (c i) (r i) ⊆ jordanInterior J) :
    closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hav : Disjoint (closedTerminalCap (T i)) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro x hx hxf
    exact (hbd (hAf ▸ hxf)) (mem_iUnion.mpr ⟨i, hx⟩)
  have hcover : closedTerminalCap (T i) ⊆ A ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxa : x ∈ A
    · exact Or.inl hxa
    · exact Or.inr (fun hc => Set.disjoint_left.mp hav hx ⟨hc, hAo.interior_eq.symm ▸ hxa⟩)
  rcases (isPreconnected_closedTerminalCap (T i)).subset_or_subset hAo
    isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hcover with hs | hs
  · exact hs
  · obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf
      isClosed_closure.isOpen_compl
      (fun x hx => hs (by obtain ⟨z, hz, rfl⟩ := hx; exact ⟨z, frontier_subset_closure hz, rfl⟩))
    have hopen : IsOpen (((↑) : ℂ → Sphere) ⁻¹' W ∩ jordanInterior J) :=
      (hW.preimage OnePoint.continuous_coe).inter (jordanInterior_isOpen J)
    have hball : closedBall (c i) (r i) ⊆ ((↑) : ℂ → Sphere) ⁻¹' W ∩ jordanInterior J :=
      fun z hz => ⟨hcomp (htarget i (mem_image_of_mem _ hz)), hin hz⟩
    obtain ⟨z, hz, hzout⟩ := exists_exterior_point_near_round_hole c r hr hd i hopen hball
    have hzV : (z : Sphere) ∈ V := by
      change z ∈ ((↑) : ℂ → Sphere) ⁻¹' V
      rw [hext]
      exact hzout
    have hfi := hmap (z : Sphere) ⟨hz.1, hzV⟩
    obtain ⟨x, hx, he⟩ := hside.symm ▸
      (show (z : Sphere) ∈ V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) from
        ⟨hzV, z, hz.2, rfl⟩)
    have hfix : fi (z : Sphere) = x := by rw [← he, hf.left_inv x hx.1]
    rw [hfix] at hfi
    exact (hfi (subset_closure hx.2)).elim

end CircleDomainRigidity

end

end OAI
