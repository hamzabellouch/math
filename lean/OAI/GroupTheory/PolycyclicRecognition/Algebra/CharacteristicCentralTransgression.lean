import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CentralTransgressionHomologyExact
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralTransgressionRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicQuotientAction

namespace OAI

/-! # The actual transgression for a characteristic central subgroup -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G P : Type} [Group G] [Group P]

def subgroupQuotientExtension (C : Subgroup G) [C.Normal] :
    GroupExtension C G (G ⧸ C) where
  inl := C.subtype
  rightHom := QuotientGroup.mk' C
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    rw [Subgroup.range_subtype, QuotientGroup.ker_mk']
  rightHom_surjective := QuotientGroup.mk'_surjective C

theorem subgroupQuotientExtension_central (C : Subgroup G) [C.Normal]
    (hc : C ≤ Subgroup.center G) :
    (subgroupQuotientExtension C).inl.range ≤ Subgroup.center G := by
  simpa only [subgroupQuotientExtension, Subgroup.range_subtype] using hc

def characteristicCentralTransgressionIntertwining
    (C : Subgroup G) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center G) (α : P →* MulAut G) :
    Representation.IntertwiningMap
      (automorphismSecondHomologyRepresentation ((characteristicQuotientAut C).comp α))
      (automorphismAdditiveRepresentation ((MulAut.characteristic C).comp α)) :=
  centralTransgressionIntertwining (subgroupQuotientExtension C)
    (subgroupQuotientExtension_central C hc)
    ((MulAut.characteristic C).comp α) α ((characteristicQuotientAut C).comp α)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (normalizedExtensionSection (subgroupQuotientExtension C))

def characteristicCentralTransgression
    (C : Subgroup G) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center G) :
    groupHomology.H2 (integralTrivialCoefficient (G ⧸ C)) →ₗ[ℤ] Additive C :=
  centralExtensionTransgression (subgroupQuotientExtension C)
    (subgroupQuotientExtension_central C hc)
    (normalizedExtensionSection (subgroupQuotientExtension C))

theorem characteristicCentralTransgression_exact_H2
    (C : Subgroup G) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center G) :
    LinearMap.range (integralSecondHomologyMap (QuotientGroup.mk' C)) =
      LinearMap.ker (characteristicCentralTransgression C hc) :=
  centralExtensionTransgression_exact_H2 (subgroupQuotientExtension C)
    (subgroupQuotientExtension_central C hc) _

theorem characteristicCentralTransgression_exact_kernel
    (C : Subgroup G) [C.Characteristic] [IsMulCommutative C]
    (hc : C ≤ Subgroup.center G) :
    LinearMap.range (characteristicCentralTransgression C hc) =
      LinearMap.ker
        (((Abelianization.of : G →* Abelianization G).comp C.subtype).toAdditive.toIntLinearMap) :=
  centralExtensionTransgression_range (subgroupQuotientExtension C)
    (subgroupQuotientExtension_central C hc) _

end PolycyclicRecognition

end

end OAI
