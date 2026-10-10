import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalCentralQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyModuleFiniteness

namespace OAI

/-! # Exactness over the actual ambient quotient group ring

Ambient FP-infinity makes the kernel of the central transgression finitely
generated over the quotient ring. This does not assert that its entire source
or the central layer has finite scalar rank.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (C : Subgroup N) [C.Characteristic] [IsMulCommutative C]

def normalCentralQuotientProjection :
    quotientHomologyAction N (trivialIntegral G) 2 ⟶ normalCentralQuotientHomologyAction N C :=
  Rep.ofHom {
    toLinearMap := integralSecondHomologyMap (QuotientGroup.mk' C)
    isIntertwining' := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      change (integralSecondHomologyMap (QuotientGroup.mk' C)).comp
          (integralSecondHomologyMap (MulAut.conjNormal (H := N) g).toMonoidHom) =
        (integralSecondHomologyMap
          (characteristicQuotientAut C (MulAut.conjNormal (H := N) g)).toMonoidHom).comp
            (integralSecondHomologyMap (QuotientGroup.mk' C))
      rw [← integralSecondHomologyMap_comp, ← integralSecondHomologyMap_comp]
      congr 1 }

def normalCentralProjectionModuleMap :
    (quotientHomologyAction N (trivialIntegral G) 2).ρ.asModule →ₗ[ℤ[G ⧸ N]]
      (normalCentralQuotientHomologyAction N C).ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (normalCentralQuotientProjection N C).hom

def normalCentralTransgressionModuleMap (hc : C ≤ Subgroup.center N) :
    (normalCentralQuotientHomologyAction N C).ρ.asModule →ₗ[ℤ[G ⧸ N]]
      (normalCentralQuotientKernelAction N C hc).ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (normalCentralQuotientTransgression N C hc).hom

theorem normalCentralHomologyModule_exact (hc : C ≤ Subgroup.center N) :
    Function.Exact (normalCentralProjectionModuleMap N C)
      (normalCentralTransgressionModuleMap N C hc) := by
  intro x
  exact ((LinearMap.exact_iff).mpr
    (characteristicCentralTransgression_exact_H2 C hc).symm) x

theorem typeFPInfinity_centralTransgressionKernel_finite [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (hG : TypeFPInfinity G) (hc : C ≤ Subgroup.center N) :
    Module.Finite ℤ[G ⧸ N] (LinearMap.ker (normalCentralTransgressionModuleMap N C hc)) := by
  let : Module.Finite ℤ[G ⧸ N] (quotientHomologyAction N (trivialIntegral G) 2).ρ.asModule :=
    typeFPInfinity_normalHomologyQuotient_finite N hG 2
  rw [(normalCentralHomologyModule_exact N C hc).linearMap_ker_eq]
  infer_instance

end PolycyclicRecognition

end

end OAI
