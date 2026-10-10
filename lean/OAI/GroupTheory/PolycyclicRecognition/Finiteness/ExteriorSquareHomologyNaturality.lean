import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianH2ExteriorProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExteriorSquareRepresentation

namespace OAI

/-! # Naturality of the exterior cross product and its homological retraction -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A B : Type} [CommGroup A] [CommGroup B]

def additiveGroupLinearMap (f : A →* B) : Additive A →ₗ[ℤ] Additive B :=
  f.toAdditive.toIntLinearMap

@[simp] theorem additiveGroupLinearMap_apply (f : A →* B) (a : A) :
    additiveGroupLinearMap f (Additive.ofMul a) = Additive.ofMul (f a) := rfl

theorem exteriorSquareMap_value (f : A →* B) (a b : A) :
    exteriorPower.map 2 (additiveGroupLinearMap f)
      (exteriorSquareValue (Additive.ofMul a) (Additive.ofMul b)) =
      exteriorSquareValue (Additive.ofMul (f a)) (Additive.ofMul (f b)) := by
  rw [exteriorSquareValue, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem exteriorSquareHomology_natural (f : A →* B)
    (z : groupHomology.H2 (integralTrivialCoefficient A)) :
    exteriorSquareHomology B
        (groupHomology.map f (integralTrivialCoefficientMap f) 2 z) =
      exteriorPower.map 2 (additiveGroupLinearMap f) (exteriorSquareHomology A z) := by
  apply bilinearPairingHomology_natural f
    (exteriorSquarePairing (M := Additive A)) (exteriorSquarePairing (M := Additive B))
    (exteriorPower.map 2 (additiveGroupLinearMap f))
  exact exteriorSquareMap_value f

theorem abelianH2Class_natural (f : A →* B) (a b : A) :
    groupHomology.map f (integralTrivialCoefficientMap f) 2 (abelianH2Class a b) =
      abelianH2Class (f a) (f b) := by
  have hn := congrArg (fun F => F.hom (antisymmetricBarCycle a b))
    (groupHomology.H2π_comp_map f (integralTrivialCoefficientMap f))
  change groupHomology.map f (integralTrivialCoefficientMap f) 2 (abelianH2Class a b) =
    groupHomology.H2π (integralTrivialCoefficient B)
      (groupHomology.mapCycles₂ f (integralTrivialCoefficientMap f)
        (antisymmetricBarCycle a b)) at hn
  rw [hn]
  apply congrArg (groupHomology.H2π (integralTrivialCoefficient B))
  apply Subtype.ext
  rw [groupHomology.coe_mapCycles₂]
  change (groupHomology.chainsMap₂ f (integralTrivialCoefficientMap f))
    (Finsupp.single (a, b) 1 - Finsupp.single (b, a) 1) = _
  simp [groupHomology.chainsMap₂, integralTrivialCoefficientMap, antisymmetricBarCycle,
    Finsupp.mapDomain_sub]

theorem abelianH2ExteriorProduct_natural (f : A →* B) :
    (groupHomology.map f (integralTrivialCoefficientMap f) 2).hom.comp
        (abelianH2ExteriorProduct A) =
      (abelianH2ExteriorProduct B).comp (exteriorPower.map 2 (additiveGroupLinearMap f)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  change groupHomology.map f (integralTrivialCoefficientMap f) 2
      (abelianH2ExteriorProduct A (exteriorPower.ιMulti ℤ 2 v)) =
    abelianH2ExteriorProduct B
      (exteriorPower.map 2 (additiveGroupLinearMap f) (exteriorPower.ιMulti ℤ 2 v))
  rw [hv]
  change groupHomology.map f (integralTrivialCoefficientMap f) 2
      (abelianH2ExteriorProduct A (exteriorSquareValue (v 0) (v 1))) =
    abelianH2ExteriorProduct B
      (exteriorPower.map 2 (additiveGroupLinearMap f) (exteriorSquareValue (v 0) (v 1)))
  exact (congrArg (groupHomology.map f (integralTrivialCoefficientMap f) 2)
    (abelianH2ExteriorProduct_value A (v 0).toMul (v 1).toMul)).trans
      ((abelianH2Class_natural f (v 0).toMul (v 1).toMul).trans
        ((congrArg (abelianH2ExteriorProduct B)
          (exteriorSquareMap_value f (v 0).toMul (v 1).toMul)).trans
            (abelianH2ExteriorProduct_value B (f (v 0).toMul) (f (v 1).toMul))).symm)

end PolycyclicRecognition

end

end OAI
