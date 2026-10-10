import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentFirstHomologyDimension
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # Naturality of the actual first-homology abelianization map -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G H : Type} [Group G] [Group H]

def groupIntegralTrivialCoefficientMap (f : G →* H) :
    integralTrivialCoefficient G ⟶ Rep.res f (integralTrivialCoefficient H) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem integralH1AbelianizationEquiv_single (g : G) (c : ℤ) :
    integralH1AbelianizationEquiv
      (groupHomology.H1π (integralTrivialCoefficient G)
        ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient G)).inv
          (Finsupp.single g c))) = c • Additive.ofMul (Abelianization.of g) := by
  change TensorProduct.rid ℤ (Additive (Abelianization G))
    (groupHomology.H1AddEquivOfIsTrivial (integralTrivialCoefficient G)
      (groupHomology.H1π (integralTrivialCoefficient G)
        ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient G)).inv
          (Finsupp.single g c)))) = _
  rw [groupHomology.H1AddEquivOfIsTrivial_single, TensorProduct.rid_tmul]

theorem integralH1_map_single (f : G →* H) (g : G) (c : ℤ) :
    groupHomology.map f (groupIntegralTrivialCoefficientMap f) 1
      (groupHomology.H1π (integralTrivialCoefficient G)
        ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient G)).inv
          (Finsupp.single g c))) =
    groupHomology.H1π (integralTrivialCoefficient H)
      ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient H)).inv
        (Finsupp.single (f g) c)) := by
  rw [groupHomology.H1π_comp_map_apply]
  apply congrArg (groupHomology.H1π (integralTrivialCoefficient H))
  apply Subtype.ext
  change groupHomology.chainsMap₁ f (groupIntegralTrivialCoefficientMap f)
    (Finsupp.single g c) = Finsupp.single (f g) c
  simp [groupHomology.chainsMap₁, groupIntegralTrivialCoefficientMap]

theorem integralH1AbelianizationEquiv_natural (f : G →* H)
    (x : groupHomology.H1 (integralTrivialCoefficient G)) :
    integralH1AbelianizationEquiv
      (groupHomology.map f (groupIntegralTrivialCoefficientMap f) 1 x) =
    (Abelianization.map f).toAdditive.toIntLinearMap
      (integralH1AbelianizationEquiv x) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (groupHomology.H1π (integralTrivialCoefficient G))).mp inferInstance x
  have hz : z = (groupHomology.cycles₁IsoOfIsTrivial
      (integralTrivialCoefficient G)).inv z.val := by apply Subtype.ext; rfl
  rw [hz]
  generalize z.val = v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single g c =>
    rw [integralH1_map_single, integralH1AbelianizationEquiv_single,
      integralH1AbelianizationEquiv_single, map_smul]
    rfl

end PolycyclicRecognition

end

end OAI
