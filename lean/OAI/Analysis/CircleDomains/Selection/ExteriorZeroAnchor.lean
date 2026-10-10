import OAI.Analysis.CircleDomains.Topology.SphereCoreExhaustion

namespace OAI

/-! A fixed quotient neighborhood of infinity contains the image of a
sufficiently far exterior region in the physical sphere. -/

open Set Function Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_exterior_in_quotient_neighborhood
    {π : Sphere → Sphere} (hπ : Continuous π) {E : Set Sphere}
    (hE : π OnePoint.infty ∈ interior E) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → π (z : Sphere) ∈ E := by
  let V := π ⁻¹' interior E
  have hV : IsOpen V := isOpen_interior.preimage hπ
  have hinf : OnePoint.infty ∈ V := hE
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' V)ᶜ :=
    ((OnePoint.isOpen_iff_of_mem hinf).mp hV).2
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, ?_⟩
  intro z hz
  apply interior_subset
  by_contra h
  exact (not_lt_of_ge hz) (hbound z h)

end CircleDomainRigidity

end OAI
