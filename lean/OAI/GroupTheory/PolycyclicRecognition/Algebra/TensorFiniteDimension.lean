import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerProjectiveCoefficientDimension

namespace OAI

/-! # Tensoring a finite-dimensional coefficient with an integer-projective module -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem integerProjective_tensor_dimension_le (C : Rep.{0} ℤ G)
    [Module.Projective ℤ C] (B : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE B d) : HasProjectiveDimensionLE (C ⊗ B) d := by
  induction d generalizing B with
  | zero =>
    let : Projective B := (projective_iff_hasProjectiveDimensionLE_zero B).mpr hd
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      (representation_tensor_projective C B)
  | succ d ih =>
    have hS := normalizedSyzygySequence_shortExact B
    have hK : HasProjectiveDimensionLE (normalizedSyzygy B) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation B) 1 (d + 1) (by omega)) hd
    have ht := representation_tensorLeft_map_shortExact C (normalizedSyzygySequence B) hS
    let : Projective (C ⊗ normalizedFreeRepresentation B) :=
      representation_tensor_projective C (normalizedFreeRepresentation B)
    exact ht.hasProjectiveDimensionLT_X₃ (d + 1) (ih _ hK)
      (hasProjectiveDimensionLT_of_ge (C ⊗ normalizedFreeRepresentation B) 1 (d + 2) (by omega))

theorem integerProjective_rightTensor_dimension_le (C : Rep.{0} ℤ G)
    [Module.Projective ℤ C] (B : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE B d) : HasProjectiveDimensionLE (B ⊗ C) d := by
  let := integerProjective_tensor_dimension_le C B d hd
  exact hasProjectiveDimensionLT_of_iso (β_ C B) (d + 1)

end PolycyclicRecognition

end

end OAI
