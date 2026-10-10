import OAI.Analysis.CircleDomains.Topology.CircleComponentCoordinates
import OAI.Analysis.CircleDomains.Topology.SphereClusterBridge

namespace OAI

/-!
# Round disk coordinates for the actual terminal assignment

The finite model's complementary disks are constructed from its circle
domain property. Their labels are exactly the physical terminal labels,
and their union is the full complement in the finite chart.
-/

open Set Function Metric

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.exists_disk_coordinates
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hV : IsCircleDomain V)
    (hinf : OnePoint.infty ∈ V) :
    ∃ (c : I → ℂ) (r : I → ℝ), (∀ i, 0 ≤ r i) ∧
      (∀ i, connectedComponentIn Vᶜ (a.point i) =
        ((↑) : ℂ → Sphere) '' closedBall (c i) (r i)) ∧
      Pairwise (Disjoint on fun i => closedBall (c i) (r i)) ∧
      ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ := by
  choose c r hr he using fun i => circleDomain_component_eq_closedBall hV hinf (a.outside i)
  refine ⟨c, r, hr, he, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    have hi : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point i) := by
      rw [he i]
      exact mem_image_of_mem _ hzi
    have hj : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point j) := by
      rw [he j]
      exact mem_image_of_mem _ hzj
    exact disjoint_left.mp (a.disjoint hij) hi hj
  · ext z
    change (z : Sphere) ∈ V ↔ z ∉ ⋃ i, closedBall (c i) (r i)
    constructor
    · intro hz hball
      obtain ⟨i, hi⟩ := mem_iUnion.mp hball
      have hc : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point i) := by
        rw [he i]
        exact mem_image_of_mem _ hi
      exact (connectedComponentIn_subset Vᶜ _ hc) hz
    · intro hz
      by_contra hnot
      obtain ⟨i, hi⟩ := a.covers (z : Sphere) hnot
      have hc := mem_connectedComponentIn (show (z : Sphere) ∈ Vᶜ from hnot)
      rw [hi, he i] at hc
      have hball : z ∈ closedBall (c i) (r i) := OnePoint.coe_injective.mem_set_image.mp hc
      exact hz (mem_iUnion.mpr ⟨i, hball⟩)

theorem terminal_disk_subset_bound
    {V : Set Sphere} {p : Sphere} {c : ℂ} {r L : ℝ}
    (he : connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' closedBall c r)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L) :
    closedBall c r ⊆ closedBall (0 : ℂ) L := by
  intro z hz
  have hzc : (z : Sphere) ∈ connectedComponentIn Vᶜ p := by
    rw [he]
    exact mem_image_of_mem _ hz
  exact OnePoint.coe_injective.mem_set_image.mp (hbound (connectedComponentIn_subset _ _ hzc))

end CircleDomainRigidity

end

end OAI
