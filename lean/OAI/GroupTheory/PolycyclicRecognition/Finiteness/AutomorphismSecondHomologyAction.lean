import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBarNaturality

namespace OAI

/-! # Automorphisms acting on actual second integral homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G H K P : Type} [Group G] [Group H] [Group K] [Group P]

def integralSecondHomologyMap (f : G →* H) :
    groupHomology.H2 (integralTrivialCoefficient G) →ₗ[ℤ]
      groupHomology.H2 (integralTrivialCoefficient H) :=
  (groupHomology.map f (groupIntegralTrivialCoefficientMap f) 2).hom

theorem integralSecondHomologyMap_comp (f : G →* H) (g : H →* K) :
    integralSecondHomologyMap (g.comp f) =
      (integralSecondHomologyMap g).comp (integralSecondHomologyMap f) := by
  have he : groupHomology.map (g.comp f) (groupIntegralTrivialCoefficientMap (g.comp f)) 2 =
      groupHomology.map f (groupIntegralTrivialCoefficientMap f) 2 ≫
        groupHomology.map g (groupIntegralTrivialCoefficientMap g) 2 := by
    rw [← groupHomology.map_comp]
    apply groupHomology.map_congr rfl
    rfl
  exact congrArg ModuleCat.Hom.hom he

theorem integralSecondHomologyMap_id :
    integralSecondHomologyMap (MonoidHom.id G) = LinearMap.id := by
  change (groupHomology.map (MonoidHom.id G) _ 2).hom = _
  have he : groupHomology.map (MonoidHom.id G)
      (groupIntegralTrivialCoefficientMap (MonoidHom.id G)) 2 = 𝟙 _ := by
    rw [← groupHomology.map_id]
    apply groupHomology.map_congr rfl
    rfl
  exact congrArg ModuleCat.Hom.hom he

def automorphismSecondHomologyRepresentation (α : P →* MulAut G) :
    Representation ℤ P (groupHomology.H2 (integralTrivialCoefficient G)) where
  toFun p := integralSecondHomologyMap (α p).toMonoidHom
  map_one' := by
    have he : (α 1).toMonoidHom = MonoidHom.id G := by rw [map_one]; rfl
    rw [he, integralSecondHomologyMap_id]
    rfl
  map_mul' p q := by
    have he : (α (p * q)).toMonoidHom = (α p).toMonoidHom.comp (α q).toMonoidHom := by
      rw [map_mul]
      rfl
    rw [he, integralSecondHomologyMap_comp]
    rfl

end PolycyclicRecognition

end

end OAI
