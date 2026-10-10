import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealMatrixSquareLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicSquareLog

namespace OAI

/-! # Free-abelian-by-cyclic groups are virtually solvable Lie lattices

No nilpotence assumption is required. Squaring the integral automorphism
permits a real logarithm, and its exponential supplies the real action.
-/

noncomputable section
namespace PolycyclicRecognition
variable {d : ℕ}

theorem realIntegralLinearEquiv_square (a : MulAut (Multiplicative (Fin d → ℤ))) :
    (realIntegralLinearEquiv (a ^ 2).toAdditive.toIntLinearEquiv).toLinearMap =
      (realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv).toLinearMap ^ 2 := by
  let f : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) := a.toAdditive.toIntLinearEquiv.toLinearMap
  let g : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) := (a ^ 2).toAdditive.toIntLinearEquiv.toLinearMap
  change realLinearExtension g = realLinearExtension f ^ 2
  apply (Pi.basisFun ℝ (Fin d)).ext
  intro i
  change realLinearExtension g ((Pi.basisFun ℝ (Fin d)) i) =
    realLinearExtension f (realLinearExtension f ((Pi.basisFun ℝ (Fin d)) i))
  rw [realLinearExtension_basis, realLinearExtension_basis, realLinearExtension_cast]
  rfl

theorem freeAbelian_cyclic_finiteIndex_lattice
    (a : MulAut (Multiplicative (Fin d → ℤ))) :
    ∃ Γ : Subgroup (Multiplicative (Fin d → ℤ) ⋊[integerPowerAction a] Multiplicative ℤ),
      Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  let A := realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv
  have hA : IsUnit A.toLinearMap := (Module.End.isUnit_iff _).mpr A.bijective
  obtain ⟨D, hD⟩ := real_linear_square_has_log A.toLinearMap hA
  apply freeAbelian_cyclic_finiteIndex_lattice_of_square_log a D
  exact hD.trans (congrArg LinearMap.toContinuousLinearMap (realIntegralLinearEquiv_square a).symm)

end PolycyclicRecognition

end

end OAI
