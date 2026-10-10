import OAI.Analysis.CircleDomains.Topology.SphereLevels
import OAI.Analysis.CircleDomains.Topology.BasePathCodes

namespace OAI

/-! A physical ball compactly contained in the domain descends to an open
quotient neighborhood with exactly that ball as its full inverse image. -/

open Set Function Metric Topology
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem component_collapse_preimage_image_subset_domain
    (G : Set Sphere) (π : Sphere → Sphere)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (S : Set Sphere) (hS : S ⊆ G) : π ⁻¹' (π '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hr y x).mp hxy with h | ⟨hg, _⟩
    · exact h ▸ hy
    · exact (hg (hS hy)).elim
  · exact fun hx => mem_image_of_mem π hx

variable [MeasurableSpace C(PathTime, Sphere)]

theorem quotient_interior_ball
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Sphere) {r : ℝ} (hrpos : 0 < r)
    (hball : closedBall p r ⊆ d.physicalDomain) :
    IsOpen (π '' ball p r) ∧ closure (π '' ball p r) ⊆ d.quotientDomain ∧
      π ⁻¹' (π '' ball p r) = ball p r ∧ π p ∈ π '' ball p r := by
  have hsat := component_collapse_preimage_image_subset_domain d.physicalDomain π hr
    (ball p r) (ball_subset_closedBall.trans hball)
  have hopen : IsOpen (π '' ball p r) :=
    (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp (by rw [hsat]; exact isOpen_ball)
  refine ⟨hopen, ?_, hsat, mem_image_of_mem π (mem_ball_self hrpos)⟩
  apply (closure_minimal (image_mono ball_subset_closedBall)
    (hclosed _ isClosed_closedBall)).trans
  rintro x ⟨y, hy, rfl⟩
  rw [← he ⟨y, hball hy⟩]
  exact (d.domainEquiv ⟨y, hball hy⟩).property

end CircleDomainRigidity

end

end OAI
