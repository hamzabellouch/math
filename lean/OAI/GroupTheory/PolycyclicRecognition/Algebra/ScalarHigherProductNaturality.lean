import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarHigherExteriorDetection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarProductNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomologyNaturality

namespace OAI

/-! # Naturality of the higher exterior cross product over every field -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K] {A B : Type} [CommGroup A] [CommGroup B]

theorem scalarHigherExteriorProduct_natural (f : A →* B) (n : ℕ) :
    ((groupHomology.map f (integralTrivialCoefficientMap f) (n + 1)).hom.baseChange K).comp
        (scalarHigherExteriorProduct K A n) =
      (scalarHigherExteriorProduct K B n).comp
        (exteriorPower.map (n + 1) ((additiveGroupLinearMap f).baseChange K)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.coe_multilinearMap_injective
  apply tensorMultilinear_ext
  intro v
  change ((groupHomology.map f (integralTrivialCoefficientMap f) (n + 1)).hom.baseChange K)
      (scalarHigherExteriorProduct K A n
        (exteriorPower.ιMulti K (n + 1) (fun i => scalarTensorUnit K _ (v i)))) =
    scalarHigherExteriorProduct K B n
      (exteriorPower.map (n + 1) ((additiveGroupLinearMap f).baseChange K)
        (exteriorPower.ιMulti K (n + 1) (fun i => scalarTensorUnit K _ (v i))))
  rw [scalarHigherExteriorProduct_value, scalarHigherBarAlternating_unit,
    exteriorPower.map_apply_ιMulti]
  have he : ((additiveGroupLinearMap f).baseChange K) ∘
      (fun i => scalarTensorUnit K (Additive A) (v i)) =
      (fun i => scalarTensorUnit K (Additive B) (additiveGroupLinearMap f (v i))) := by
    funext i
    rfl
  rw [he, scalarHigherExteriorProduct_value, scalarHigherBarAlternating_unit]
  change (1 : K) ⊗ₜ[ℤ]
      groupHomology.map f (integralTrivialCoefficientMap f) (n + 1)
        (tupleBarProductClass (fun i => (v i).toMul)) =
    (1 : K) ⊗ₜ[ℤ] tupleBarProductClass (fun i => f (v i).toMul)
  rw [tupleBarProductClass_natural]
  rfl

end PolycyclicRecognition

end

end OAI
