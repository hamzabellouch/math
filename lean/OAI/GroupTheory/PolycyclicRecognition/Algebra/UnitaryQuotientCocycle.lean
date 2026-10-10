import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryCocycle
import Mathlib.Topology.Algebra.Group.Quotient

namespace OAI

/-! # Descending a central-trivial unitary cocycle to the central quotient -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hz : ∀ z : Subgroup.center G, ρ z = 1)

def centerQuotientUnitary : (G ⧸ Subgroup.center G) →* (E ≃ₗᵢ[ℝ] E) :=
  QuotientGroup.lift (Subgroup.center G) ρ (fun g hg => hz ⟨g, hg⟩)

theorem centerQuotientUnitary_mk (g : G) :
    centerQuotientUnitary ρ hz (QuotientGroup.mk g) = ρ g := rfl

variable {ρ hz} (b : G → E) (hb : IsUnitaryCocycle ρ b)
  (hbz : ∀ z : Subgroup.center G, b z = 0)

def centerQuotientCocycle : G ⧸ Subgroup.center G → E :=
  Quotient.lift b (fun a c hac => by
    have hm : a⁻¹ * c ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hac
    have hzero := hbz ⟨a⁻¹ * c, hm⟩
    have he := hb a (a⁻¹ * c)
    simpa only [mul_inv_cancel_left, hzero, map_zero, add_zero] using he.symm)

theorem centerQuotientCocycle_mk (g : G) :
    centerQuotientCocycle b hb hbz (QuotientGroup.mk g) = b g := rfl

theorem centerQuotientCocycle_isCocycle :
    IsUnitaryCocycle (centerQuotientUnitary ρ hz) (centerQuotientCocycle b hb hbz) := by
  intro q r
  induction q using QuotientGroup.induction_on with | H g =>
    induction r using QuotientGroup.induction_on with | H h =>
      exact hb g h

variable [TopologicalSpace G]

theorem centerQuotientCocycle_continuous (hbc : Continuous b) :
    Continuous (centerQuotientCocycle b hb hbz) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
  exact hbc

theorem centerQuotientUnitary_continuous (hρ : ∀ v : E, Continuous (fun g : G => ρ g v))
    (v : E) : Continuous (fun q : G ⧸ Subgroup.center G => centerQuotientUnitary ρ hz q v) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
  exact hρ v

end PolycyclicRecognition

end

end OAI
