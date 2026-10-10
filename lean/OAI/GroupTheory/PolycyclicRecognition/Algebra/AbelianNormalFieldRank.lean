import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalExteriorInjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFiniteRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InfiniteFieldExteriorRank
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Finiteness.Descent

namespace OAI

/-! # Finite scalar rank of abelian kernels over every field -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct MonoidAlgebra IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

theorem abelian_normal_kernel_finite_infinite_field_rank (K : Type) [Field K] [Infinite K]
    (h : TypeFPInfinity G) : FiniteDimensional K (K ⊗[ℤ] Additive N) := by
  let ρ := scalarExtendedRepresentation K (abelianKernelQuotientConjugationAction N)
  let := abelianKernelQuotient_finite N
  let : Module.Finite K[G ⧸ N] ρ.asModule :=
    scalarExtendedRepresentation_finite K (abelianKernelQuotientConjugationAction N)
  apply finite_rank_of_finite_higher_exterior_infinite ρ
  intro n
  exact typeFPInfinity_abelianNormalHigherExterior_finite_all_char K N h n

theorem abelian_normal_kernel_finite_field_rank (K : Type) [Field K]
    (h : TypeFPInfinity G) : FiniteDimensional K (K ⊗[ℤ] Additive N) := by
  let L := AlgebraicClosure K
  let : FiniteDimensional L (L ⊗[ℤ] Additive N) :=
    abelian_normal_kernel_finite_infinite_field_rank N L h
  let e : L ⊗[K] (K ⊗[ℤ] Additive N) ≃ₗ[L] L ⊗[ℤ] Additive N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L (Additive N)
  let : Module.Finite L (L ⊗[K] (K ⊗[ℤ] Additive N)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

end PolycyclicRecognition

end

end OAI
