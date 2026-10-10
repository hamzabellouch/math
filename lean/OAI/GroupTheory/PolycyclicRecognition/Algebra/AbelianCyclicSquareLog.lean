import OAI.GroupTheory.PolycyclicRecognition.Lattices.AbelianCyclicLogarithmLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicSquareIndex

namespace OAI

/-! # A logarithm of the squared automorphism suffices for the lattice

The square gives a concrete finite-index subgroup. Thus the matrix logarithm
needed for the real action may be taken after this finite-index passage.
-/

noncomputable section
namespace PolycyclicRecognition
variable {d : ℕ}

theorem freeAbelian_cyclic_finiteIndex_lattice_of_square_log
    (a : MulAut (Multiplicative (Fin d → ℤ)))
    (D : AbelianRealSpace d →L[ℝ] AbelianRealSpace d)
    (hD : NormedSpace.exp D =
      (realIntegralLinearEquiv (a ^ 2).toAdditive.toIntLinearEquiv).toContinuousLinearEquiv.toContinuousLinearMap) :
    ∃ Γ : Subgroup (Multiplicative (Fin d → ℤ) ⋊[integerPowerAction a] Multiplicative ℤ),
      Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨S, Λ, hΛ, ⟨e⟩⟩ := freeAbelian_cyclic_lattice_of_linear_log (a ^ 2) D hD
  exact ⟨(cyclicSquareMap a).range, cyclicSquareMap_range_finiteIndex a,
    S, Λ, hΛ, ⟨(cyclicSquareRangeEquiv a).symm.trans e⟩⟩

end PolycyclicRecognition

end

end OAI
