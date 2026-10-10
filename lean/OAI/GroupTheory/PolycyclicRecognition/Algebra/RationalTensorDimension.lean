import OAI.GroupTheory.PolycyclicRecognition.Algebra.TensorFiniteDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCoefficientSequence
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialProjectiveTelescope

namespace OAI

/-! # Rational tensoring costs at most one integral projective dimension -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped DirectSum
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule DirectSum.instModule
variable {G : Type} [Group G]

theorem rationalTensor_dimension_le (B : Rep.{0} ℤ G) [Module.Flat ℤ B]
    (d : ℕ) (hd : HasProjectiveDimensionLE B d) :
    HasProjectiveDimensionLE (B ⊗ Rep.trivial ℤ G ℚ) (d + 1) := by
  let c := rationalCoefficientColimit G
  let S := c.telescopeSequence
  let : Module.Projective ℤ S.X₁ := by
    change Module.Projective ℤ (⨁ _ : ℕ, ℤ)
    infer_instance
  let : Module.Projective ℤ S.X₂ := by
    change Module.Projective ℤ (⨁ _ : ℕ, ℤ)
    infer_instance
  have h₁ := integerProjective_rightTensor_dimension_le S.X₁ B d hd
  have h₂ := integerProjective_rightTensor_dimension_le S.X₂ B d hd
  let := h₂
  have hs := representation_tensorLeft_map_shortExact B S c.telescopeSequence_shortExact
  exact hs.hasProjectiveDimensionLT_X₃ (d + 1) h₁
    (hasProjectiveDimensionLT_of_ge (B ⊗ S.X₂) (d + 1) (d + 2) (by omega))

theorem rationalTensor_left_dimension_le (B : Rep.{0} ℤ G) [Module.Flat ℤ B]
    (d : ℕ) (hd : HasProjectiveDimensionLE B d) :
    HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ ⊗ B) (d + 1) := by
  let := rationalTensor_dimension_le B d hd
  exact hasProjectiveDimensionLT_of_iso (β_ B (Rep.trivial ℤ G ℚ)) (d + 2)

end PolycyclicRecognition

end

end OAI
