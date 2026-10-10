import OAI.Analysis.CircleDomains.Topology.RetainedImageBoundary

namespace OAI

/-! Select exactly the finite round holes inside a retained Jordan curve.
Its punctured closed side is therefore contained in the actual target
domain, including its outer boundary. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem round_hole_jordan_side (H : ℂ ≃ₜ ℂ) (c : ℂ) (r : ℝ)
    (havoid : Disjoint (closedBall c r) (frontier (jordanInterior H))) :
    closedBall c r ⊆ jordanInterior H ∨
      Disjoint (closedBall c r) (closure (jordanInterior H)) := by
  have ho := jordanInterior_isOpen H
  have hs : closedBall c r ⊆ jordanInterior H ∪ (closure (jordanInterior H))ᶜ := by
    intro z hz
    by_cases hi : z ∈ jordanInterior H
    · exact Or.inl hi
    · exact Or.inr (fun hc => Set.disjoint_left.mp havoid hz
        ⟨hc, ho.interior_eq.symm ▸ hi⟩)
  rcases isPreconnected_closedBall.subset_or_subset ho isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))) hs with h | h
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.mpr (fun _ hz hc => h hz hc))

 theorem exists_round_holes_inside_jordan
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ)
    (V : Set Sphere) (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V) :
    ∃ (m : ℕ) (κ : Fin m → I), Injective κ ∧
      (∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H) ∧
      (∀ i, i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior H) ∧
      closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) =
        closure (jordanInterior H) ∩ ((↑) : ℂ → Sphere) ⁻¹' V := by
  classical
  let A := {i : I | closedBall (c i) (r i) ⊆ jordanInterior H}
  let e := (Fintype.equivFin A).symm
  let κ : Fin (Fintype.card A) → I := fun j => (e j).val
  have hk : Injective κ := Subtype.val_injective.comp e.injective
  have hki (j) : closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H := (e j).property
  have hrange (i : I) : i ∈ range κ ↔ closedBall (c i) (r i) ⊆ jordanInterior H := by
    constructor
    · rintro ⟨j, rfl⟩
      exact hki j
    · intro hi
      exact ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩
  refine ⟨Fintype.card A, κ, hk, hki, hrange, ?_⟩
  ext z
  rw [mem_sdiff, mem_inter_iff, hext, mem_compl_iff]
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hu
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    have hav : Disjoint (closedBall (c i) (r i)) (frontier (jordanInterior H)) := by
      apply Set.disjoint_left.mpr
      intro x hx hxf
      have hv : (x : Sphere) ∈ V := hbd ⟨x, hxf, rfl⟩
      rw [← mem_preimage, hext] at hv
      exact hv (mem_iUnion.mpr ⟨i, hx⟩)
    rcases round_hole_jordan_side H (c i) (r i) hav with hin | hout
    · obtain ⟨j, hj⟩ := (hrange i).mpr hin
      apply hnot
      exact mem_iUnion.mpr ⟨j, hj.symm ▸ hi⟩
    · exact Set.disjoint_left.mp hout hi hz
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    exact hnot (mem_iUnion.mpr ⟨κ j, hj⟩)

end CircleDomainRigidity

end

end OAI
