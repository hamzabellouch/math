import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExactTensorCoefficient
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedProjectiveTower

namespace OAI

/-! # The projective tower tensored with the coefficient algebra

For a coefficient projective over the integers, tensoring the normalized
integral tower gives an actual projective tower, based at that coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

variable (A : Rep.{0} ℤ G) [Module.Projective ℤ A]

def tensorNormalizedProjectiveTower : IntegralProjectiveTower G where
  obj n := A ⊗ (normalizedProjectiveTower (trivialIntegral G)).obj n
  projectiveObj n := A ⊗ (normalizedProjectiveTower (trivialIntegral G)).projectiveObj n
  projective n := representation_tensor_projective A _
  ι n := (tensorLeft A).map ((normalizedProjectiveTower (trivialIntegral G)).ι n)
  π n := (tensorLeft A).map ((normalizedProjectiveTower (trivialIntegral G)).π n)
  zero n := by
    rw [← CategoryTheory.Functor.map_comp, (normalizedProjectiveTower (trivialIntegral G)).zero,
      CategoryTheory.Functor.map_zero]
  shortExact n := representation_tensorLeft_map_shortExact A
    ((normalizedProjectiveTower (trivialIntegral G)).sequence n)
    ((normalizedProjectiveTower (trivialIntegral G)).shortExact n)

def tensorNormalizedTowerBaseIso : (tensorNormalizedProjectiveTower A).obj 0 ≅ A :=
  ρ_ A

def tensorNormalizedTowerCompletion (p : ℕ) :
    (tensorNormalizedProjectiveTower A).Cohomology p ≃ₗ[ℤ]
      ShiftedCompletedCohomology p A :=
  (tensorNormalizedProjectiveTower A).completeCohomologyEquiv A
    (tensorNormalizedTowerBaseIso A) p

end PolycyclicRecognition

end

end OAI
