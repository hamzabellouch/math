import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TensorProjectiveTower
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTowerDimension

namespace OAI

/-! # The integral dimension bound for an integer-projective coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem integerProjectiveCoefficient_dimension_le (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] (d : ℕ) (hd : HasProjectiveDimensionLE (trivialIntegral G) d) :
    HasProjectiveDimensionLE A d := by
  have hΩ : HasProjectiveDimensionLE
      ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) 0 :=
    iteratedNormalizedSyzygy_projectiveDimension (trivialIntegral G) d 0
      (by simpa only [Nat.add_zero] using hd)
  have hproj : Projective ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr hΩ
  let : Projective ((tensorNormalizedProjectiveTower A).obj d) :=
    @representation_tensor_projective G _ A
      ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) inferInstance hproj
  let := (tensorNormalizedProjectiveTower A).dimension_of_projective_tail d
  exact hasProjectiveDimensionLT_of_iso (tensorNormalizedTowerBaseIso A) (d + 1)

theorem smallCoefficient_dimension_le_of_integral_dimension (G : Type) [Group G] [Countable G]
    (H : Subgroup G) (d : ℕ) (hd : HasProjectiveDimensionLE (trivialIntegral H) d) :
    HasProjectiveDimensionLE (Rep.res H.subtype (smallCoefficientRepresentation G)) d :=
  integerProjectiveCoefficient_dimension_le _ d hd

end PolycyclicRecognition

end

end OAI
