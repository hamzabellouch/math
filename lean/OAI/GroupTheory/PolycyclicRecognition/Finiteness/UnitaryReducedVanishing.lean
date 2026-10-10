import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCocycleSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundledCentralAverage

namespace OAI

/-! # The unitary formulation of reduced cocycle vanishing -/

noncomputable section

namespace PolycyclicRecognition

universe u v

open Set

def UnitaryReducedVanishing (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)),
    (∀ x : E, (∀ g, ρ g x = x) → x = 0) →
    (∀ x : E, Continuous (fun g => ρ g x)) →
    ∀ b : G → E, Continuous b → IsUnitaryCocycle ρ b →
    ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε

variable {G : Type u} [Group G] [TopologicalSpace G]

theorem UnitaryReducedVanishing.to_reduced
    (h : UnitaryReducedVanishing.{u, v} G)
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E] :
    ReducedCohomologyInput G E := by
  intro hfix hact b hbc hb Q hQ ε hε
  exact h E (isometricLinearAction (G := G) (E := E)) hfix hact b hbc hb Q hQ ε hε

theorem unitaryReducedVanishing_of_subsingleton [Subsingleton G] :
    UnitaryReducedVanishing.{u, v} G := by
  intro E _ _ _ ρ hfix _ b _ _ Q _ ε hε
  have hz (x : E) : x = 0 := hfix x (fun g => by
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg, ρ.map_one]
    rfl)
  refine ⟨0, fun q _ => ?_⟩
  simp only [hz (b q), map_zero, add_zero, sub_self, norm_zero]
  exact hε.le

end PolycyclicRecognition

end

end OAI
