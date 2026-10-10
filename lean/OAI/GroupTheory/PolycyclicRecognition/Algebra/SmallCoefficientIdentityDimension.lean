import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientIdentityCycle
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTowerDimension

namespace OAI

/-! # A vanishing unit cocycle splits the coefficient-ring syzygy

Multiplication in the coefficient ring extends an integral cochain to a
coefficient-linear cochain. Applied to a primitive of the identity cocycle,
this splits the next kernel and gives finite projective dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] TensorProduct.instModule
variable (G : Type) [Group G] [Countable G]

theorem smallCoefficientIdentityClass_zero_projective (n : ℕ)
    (h : smallCoefficientIdentityClass G (n + 1) = 0) :
    Projective ((smallCoefficientTower G).obj (n + 1)) := by
  let C := (normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
    ((smallCoefficientTower G).obj (n + 1))
  obtain ⟨r, hr⟩ := cochain_boundary_of_class_zero C n
    (smallCoefficientIdentityCycle G (n + 1)) h
  rw [smallCoefficientIdentityCycle_projection] at hr
  change (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫ r =
    smallCoefficientIdentityCochain G (n + 1) at hr
  let F := tensorLeft (smallCoefficientRepresentation G)
  let T := smallCoefficientTower G
  let A := (iteratedNormalizedSyzygy (n + 1)).obj (trivialIntegral G)
  let π := normalizedResolutionProjection (trivialIntegral G) (n + 1)
  let ι := kernel.ι (normalizedFreeAugmentation
    ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
  let s : T.projectiveObj n ⟶ T.obj (n + 1) := F.map r ≫ smallCoefficientTensorMultiply A
  have hprimitive : (π ≫ ι) ≫ r = π ≫ smallCoefficientTensorUnit A := by
    rw [normalizedResolutionComplex_d] at hr
    exact hr
  let : Epi π := inferInstanceAs (Epi (normalizedFreeAugmentation A))
  have hsplit : T.ι n ≫ s = 𝟙 _ :=
    smallCoefficientTensor_split_of_unit_homotopy π ι r hprimitive
  exact (show Retract (T.obj (n + 1)) (T.projectiveObj n) from
    ⟨T.ι n, s, hsplit⟩).projective

theorem smallCoefficient_finite_dimension_of_identityClass_zero (n : ℕ)
    (h : smallCoefficientIdentityClass G (n + 1) = 0) :
    HasProjectiveDimensionLE (smallCoefficientRepresentation G) (n + 1) := by
  let := smallCoefficientIdentityClass_zero_projective G n h
  have hd := (smallCoefficientTower G).dimension_of_projective_tail (n + 1)
  let := hd
  exact hasProjectiveDimensionLT_of_iso
    (tensorNormalizedTowerBaseIso (smallCoefficientRepresentation G)) (n + 2)

end PolycyclicRecognition

end

end OAI
