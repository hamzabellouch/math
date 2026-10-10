import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryCocycle

namespace OAI

/-! # Central averaging in the bundled unitary notation -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem IsUnitaryCocycle.small_correction_of_no_central_invariants
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (hcenter : ∀ v : E, (∀ z : Subgroup.center G, ρ z v = v) → v = 0)
    (hbc : Continuous b) (Q : Set G) (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  let : SMulCommClass G ℝ E := ⟨fun g c x => (ρ g).map_smul c x⟩
  exact exists_small_correction_of_no_central_invariants hcenter b hbc hb Q hQ hε

end PolycyclicRecognition

end

end OAI
