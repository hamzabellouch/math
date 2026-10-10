import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalCentralQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients

namespace OAI

/-! # A central derived layer is a quotient of actual second homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear

theorem characteristicCentralTransgression_surjective
    {H : Type} [Group H] (C : Subgroup H) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center H) (hd : C ≤ commutator H) :
    Function.Surjective (characteristicCentralTransgression C hc) := by
  rw [← LinearMap.range_eq_top, characteristicCentralTransgression_exact_kernel]
  have he : ((Abelianization.of : H →* Abelianization H).comp C.subtype).toAdditive.toIntLinearMap =
      (0 : Additive C →ₗ[ℤ] Additive (Abelianization H)) := by
    apply LinearMap.ext
    intro c
    have hk : c.toMul.val ∈ (Abelianization.of : H →* Abelianization H).ker := by
      rw [Abelianization.ker_of]
      exact hd c.toMul.property
    exact congrArg Additive.ofMul hk
  rw [he, LinearMap.ker_zero]

theorem normalCentralDerived_finite_of_quotient_H2_finite
    {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (C : Subgroup N) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center N) (hd : C ≤ commutator N)
    (h : IntegralRepresentationFinite (G ⧸ N) (normalCentralQuotientHomologyAction N C)) :
    IntegralRepresentationFinite (G ⧸ N) (normalCentralQuotientKernelAction N C hc) := by
  let f := normalCentralQuotientTransgression N C hc
  have hf : Function.Surjective f := characteristicCentralTransgression_surjective C hc hd
  let : Epi f := (Rep.epi_iff_surjective f).mpr hf
  exact h.of_epi f

end PolycyclicRecognition

end

end OAI
