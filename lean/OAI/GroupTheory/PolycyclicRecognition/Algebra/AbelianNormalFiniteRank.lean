import OAI.GroupTheory.PolycyclicRecognition.Algebra.HigherExteriorFiniteRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicKernelRank
import Mathlib.LinearAlgebra.Dimension.Localization

namespace OAI

/-! # Finite rational rank of every abelian kernel in the abelian-quotient case

Actual FP-infinity supplies all higher homology modules. Their natural maps
to exterior powers, followed by the free-orbit obstruction, give finite rank
without a cyclic quotient or a rank assumption on the kernel.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative TensorProduct MonoidAlgebra
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

theorem abelian_normal_kernel_finite_scalar_rank (K : Type) [Field K] [CharZero K]
    (h : TypeFPInfinity G) : FiniteDimensional K (K ⊗[ℤ] Additive N) := by
  let ρ := scalarExtendedRepresentation K (abelianKernelQuotientConjugationAction N)
  let := abelianKernelQuotient_finite N
  let : Module.Finite K[G ⧸ N] ρ.asModule :=
    scalarExtendedRepresentation_finite K (abelianKernelQuotientConjugationAction N)
  exact finite_rank_of_finite_higher_exterior ρ
    (fun n => typeFPInfinity_abelianNormalHigherExterior_finite K N h n)

theorem abelian_normal_kernel_finite_rank (h : TypeFPInfinity G) :
    ∃ d : ℕ, Module.rank ℤ (Additive N) ≤ d := by
  let := abelian_normal_kernel_finite_scalar_rank N ℚ h
  refine ⟨Module.finrank ℚ (ℚ ⊗[ℤ] Additive N), ?_⟩
  rw [← (TensorProduct.isBaseChange (R := ℤ) (S := ℚ) (M := Additive N)).rank_eq,
    ← Module.finrank_eq_rank]

end PolycyclicRecognition

end

end OAI
